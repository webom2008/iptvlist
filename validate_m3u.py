#!/usr/bin/env python3
"""
M3U Playlist Validator
Reads playlist URLs from playlist_urls.txt, validates each stream,
and saves working channels to a new M3U file.
No third-party dependencies required.
"""

import urllib.request
import urllib.error
import urllib.parse
import socket
import threading
import time
import sys
import os
import re
import argparse
from queue import Queue, Empty
from datetime import datetime


# ── defaults ────────────────────────────────────────────────────────────────
DEFAULT_TIMEOUT      = 10      # seconds per stream check
DEFAULT_PL_TIMEOUT   = 30      # seconds for downloading a playlist
DEFAULT_WORKERS      = 20      # concurrent validation threads
DEFAULT_INPUT        = "playlist_urls.txt"
DEFAULT_OUTPUT       = "valid_channels.m3u"
DEFAULT_RETRY        = 1       # retry count on failure
VALID_CONTENT_TYPES  = (
    "application/vnd.apple.mpegurl",
    "application/x-mpegurl",
    "video/mp2t",
    "video/mp4",
    "video/x-flv",
    "video/mpeg",
    "application/octet-stream",
    "text/plain",              # some servers return this for .m3u8
    "audio/mpegurl",
    "audio/x-mpegurl",
)
# ── ─────────────────────────────────────────────────────────────────────────


def log(msg: str, level: str = "INFO") -> None:
    ts = datetime.now().strftime("%H:%M:%S")
    print(f"[{ts}] [{level:5s}] {msg}", flush=True)


def install_proxy(proxy: str | None) -> None:
    """
    Install a global urllib opener with optional proxy.
    Also picks up HTTP_PROXY / HTTPS_PROXY env vars automatically.
    Call once at startup before any network activity.
    """
    proxies: dict[str, str] = {}
    # env vars (lowercase takes precedence in urllib, but be explicit)
    for var in ("http_proxy", "HTTP_PROXY", "https_proxy", "HTTPS_PROXY"):
        val = os.environ.get(var, "")
        if val:
            scheme = "https" if "https" in var.lower() else "http"
            proxies.setdefault(scheme, val)
    # explicit --proxy flag overrides env
    if proxy:
        proxies["http"] = proxy
        proxies["https"] = proxy

    handlers: list = []
    if proxies:
        handlers.append(urllib.request.ProxyHandler(proxies))
        log(f"Using proxy: {next(iter(proxies.values()))}")
    else:
        # explicitly disable system proxy discovery (avoids macOS keychain delays)
        handlers.append(urllib.request.ProxyHandler({}))

    opener = urllib.request.build_opener(*handlers)
    urllib.request.install_opener(opener)


def build_request(url: str, method: str = "HEAD") -> urllib.request.Request:
    req = urllib.request.Request(url, method=method)
    req.add_header("User-Agent",
        "Mozilla/5.0 (AppleWebKit/537.36) Chrome/120 Safari/537.36 VLC/3.0")
    req.add_header("Accept", "*/*")
    req.add_header("Connection", "close")
    return req


def fetch_url(url: str, timeout: int, binary: bool = False, referer: str = ""):
    """
    Return (content, final_url) or raise.
    Streams in 64 KB chunks so the per-chunk socket timeout never fires
    on large playlists delivered over slow/proxied connections.
    """
    req = build_request(url, method="GET")
    if referer:
        req.add_header("Referer", referer)
    chunks: list[bytes] = []
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        final_url = resp.geturl()
        while True:
            chunk = resp.read(65536)   # 64 KB — each read must finish within timeout
            if not chunk:
                break
            chunks.append(chunk)
    raw = b"".join(chunks)
    return (raw if binary else raw.decode("utf-8", errors="replace")), final_url


def is_m3u_content(text: str) -> bool:
    first = text.lstrip()[:50]
    return first.startswith("#EXTM3U") or first.startswith("#EXTINF")


def parse_m3u(text: str) -> list[dict]:
    """Parse M3U text, return list of channel dicts."""
    channels = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line.startswith("#EXTINF"):
            info_line = line
            # collect any extra tags between #EXTINF and the URL
            extra_lines = []
            i += 1
            while i < len(lines) and lines[i].strip().startswith("#"):
                extra_lines.append(lines[i].strip())
                i += 1
            if i < len(lines):
                url = lines[i].strip()
                if url and not url.startswith("#"):
                    channels.append({
                        "extinf": info_line,
                        "extra":  extra_lines,
                        "url":    url,
                    })
        i += 1
    return channels


def is_html(data: bytes) -> bool:
    """Return True if the bytes look like an HTML error page."""
    sniff = data.lstrip()[:100].lower()
    return sniff.startswith(b"<!doctype") or sniff.startswith(b"<html")


def resolve_segment_url(segment: str, base_url: str) -> str:
    """Resolve a possibly-relative TS segment path against the M3U8 base URL."""
    if segment.startswith(("http://", "https://")):
        return segment
    return urllib.parse.urljoin(base_url, segment)


def extract_segments(m3u8_text: str) -> list[str]:
    """Return non-comment, non-empty lines that look like media segment paths."""
    segs = []
    for line in m3u8_text.splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            segs.append(line)
    return segs


def check_segment(seg_url: str, timeout: int) -> tuple[bool, str]:
    """
    Verify one TS/media segment is actually downloadable binary data.
    Returns (ok, reason).
    """
    try:
        req = build_request(seg_url, method="GET")
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            if resp.status not in (200, 206):
                return False, f"segment HTTP {resp.status}"
            chunk = resp.read(188)          # one MPEG-TS packet = 188 bytes
            if len(chunk) == 0:
                return False, "segment empty"
            if is_html(chunk):
                return False, "segment returned HTML (IP/auth blocked)"
            ct = (resp.headers.get("Content-Type") or "").lower()
            # TS sync byte 0x47 at byte 0 is definitive proof
            if chunk[0:1] == b"\x47":
                return True, "segment TS sync byte OK"
            if chunk.startswith(b"#EXTM3U") or chunk.startswith(b"#EXT"):
                return True, "segment is sub-playlist"
            # fMP4 segment (starts with ftyp/moof/mdat box)
            if chunk[4:8] in (b"ftyp", b"moof", b"mdat", b"styp"):
                return True, "segment fMP4 box OK"
            # fallback: non-HTML binary with acceptable content-type
            if any(t in ct for t in ("video", "audio", "octet", "mpegurl", "mpeg")):
                return True, f"segment ct={ct!r}"
            return False, f"segment unrecognised content (ct={ct!r})"
    except urllib.error.HTTPError as e:
        return False, f"segment HTTP {e.code}"
    except Exception as e:
        return False, f"segment error: {type(e).__name__}: {e}"


def check_stream(url: str, timeout: int, retries: int) -> tuple[bool, str]:
    """
    Validate a stream URL.
    Returns (is_valid, reason).

    Strategy:
      1. GET the URL, read first 512 bytes
         - If HTML → reject immediately (error page)
         - If M3U8 text → extract a TS segment and verify it (deep check)
         - If binary TS/fMP4 data → accept
      2. HEAD fallback for non-M3U8 direct streams
    """
    for attempt in range(retries + 1):
        reason = "unknown"
        try:
            # ── Step 1: GET the channel URL ──────────────────────────────
            req = build_request(url, method="GET")
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                status = resp.status
                final_url = resp.geturl()
                ct = (resp.headers.get("Content-Type") or "").lower().split(";")[0].strip()

                if status not in (200, 206):
                    reason = f"HTTP {status}"
                    if status in (403, 404, 410):
                        return False, reason
                    raise ValueError(reason)

                chunk = resp.read(512)

            # ── Step 2: classify the response ────────────────────────────
            if is_html(chunk):
                return False, "returned HTML (captive portal / error page)"

            is_m3u8 = (
                chunk.lstrip()[:7] in (b"#EXTM3U", b"#EXTINF")
                or chunk.lstrip()[:4] == b"#EXT"
                or "mpegurl" in ct
                or url.lower().split("?")[0].endswith((".m3u8", ".m3u"))
            )

            if is_m3u8:
                # ── Step 3: deep-check — verify a TS segment ─────────────
                text = chunk.decode("utf-8", errors="replace")
                # read remaining playlist text (it's small)
                try:
                    req2 = build_request(url, method="GET")
                    with urllib.request.urlopen(req2, timeout=timeout) as r2:
                        text = r2.read(8192).decode("utf-8", errors="replace")
                        final_url = r2.geturl()
                except Exception:
                    pass   # use what we already have

                segments = extract_segments(text)
                if not segments:
                    return False, "M3U8 has no segments"

                # try up to 3 segments (first available wins)
                for seg in segments[:3]:
                    seg_url = resolve_segment_url(seg, final_url)
                    ok, seg_reason = check_segment(seg_url, timeout)
                    if ok:
                        return True, f"M3U8+segment OK ({seg_reason})"
                return False, f"all segments failed: {seg_reason}"  # type: ignore[possibly-undefined]

            # ── Direct stream (TS/fMP4/etc.) ─────────────────────────────
            if chunk[0:1] == b"\x47":
                return True, "direct TS stream (sync byte)"
            if chunk[4:8] in (b"ftyp", b"moof", b"mdat", b"styp"):
                return True, "direct fMP4 stream"
            if any(ct.startswith(v) for v in VALID_CONTENT_TYPES):
                if len(chunk) > 0:
                    return True, f"direct stream ct={ct!r}"
            if len(chunk) > 0:
                return False, f"unrecognised content ct={ct!r}"
            return False, "empty response"

        except urllib.error.HTTPError as e:
            reason = f"HTTP {e.code}"
            if e.code in (403, 404, 410):
                return False, reason
        except urllib.error.URLError as e:
            reason = f"URLError: {e.reason}"
        except socket.timeout:
            reason = "Timeout"
        except (ConnectionResetError, ConnectionRefusedError) as e:
            reason = f"ConnError: {e}"
        except ValueError:
            pass   # already set reason above
        except Exception as e:
            reason = f"Error: {type(e).__name__}: {e}"

        if attempt < retries:
            time.sleep(1)

    return False, reason


# ── worker thread ─────────────────────────────────────────────────────────

def worker(job_queue: Queue, results: list, timeout: int,
           retries: int, lock: threading.Lock, counter: list) -> None:
    while True:
        try:
            channel = job_queue.get(timeout=2)
        except Empty:
            break
        valid, reason = check_stream(channel["url"], timeout, retries)
        with lock:
            counter[0] += 1
            if valid:
                results.append(channel)
            # progress on same line
            done = counter[0]
            total = counter[1]
            mark = "OK" if valid else "--"
            name = extract_name(channel["extinf"])
            print(f"\r  [{done:>4}/{total}] [{mark}] {name[:60]:<60}", end="", flush=True)
        job_queue.task_done()


def extract_name(extinf: str) -> str:
    """Extract channel name from #EXTINF line."""
    m = re.search(r',(.+)$', extinf)
    return m.group(1).strip() if m else extinf


# ── playlist downloader ───────────────────────────────────────────────────

def load_playlist(url: str, pl_timeout: int) -> list[dict]:
    """Download and parse a single M3U playlist URL or local file path."""
    try:
        # local file: plain path or file:// URI
        if url.startswith("file://"):
            path = urllib.request.url2pathname(urllib.parse.urlparse(url).path)
            with open(path, encoding="utf-8", errors="replace") as f:
                text = f.read()
        elif not url.startswith(("http://", "https://")):
            # treat as a local filesystem path
            with open(url, encoding="utf-8", errors="replace") as f:
                text = f.read()
        else:
            text, _ = fetch_url(url, pl_timeout)

        if not is_m3u_content(text):
            log(f"Not an M3U playlist: {url}", "WARN")
            return []
        channels = parse_m3u(text)
        log(f"Loaded {len(channels):>4} channels from {url}")
        return channels
    except Exception as e:
        log(f"Failed to load {url}: {e}", "ERROR")
        return []


# ── output writer ─────────────────────────────────────────────────────────

def write_m3u(channels: list[dict], path: str) -> None:
    with open(path, "w", encoding="utf-8") as f:
        f.write("#EXTM3U\n")
        for ch in channels:
            f.write(ch["extinf"] + "\n")
            for extra in ch.get("extra", []):
                f.write(extra + "\n")
            f.write(ch["url"] + "\n")
    log(f"Saved {len(channels)} valid channels → {path}")


# ── main ──────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Validate M3U playlists and save working channels.")
    parser.add_argument("-i", "--input",   default=DEFAULT_INPUT,
                        help=f"File with playlist URLs, one per line (default: {DEFAULT_INPUT})")
    parser.add_argument("-o", "--output",  default=DEFAULT_OUTPUT,
                        help=f"Output M3U file (default: {DEFAULT_OUTPUT})")
    parser.add_argument("-t", "--timeout", type=int, default=DEFAULT_TIMEOUT,
                        help=f"Per-stream timeout in seconds (default: {DEFAULT_TIMEOUT})")
    parser.add_argument("-T", "--playlist-timeout", type=int, default=DEFAULT_PL_TIMEOUT,
                        help=f"Timeout for downloading a playlist (default: {DEFAULT_PL_TIMEOUT})")
    parser.add_argument("-w", "--workers", type=int, default=DEFAULT_WORKERS,
                        help=f"Concurrent validation threads (default: {DEFAULT_WORKERS})")
    parser.add_argument("-r", "--retry",   type=int, default=DEFAULT_RETRY,
                        help=f"Retry count on failure (default: {DEFAULT_RETRY})")
    parser.add_argument("-p", "--proxy",   default=None,
                        help="HTTP/HTTPS proxy URL, e.g. http://127.0.0.1:7890  "
                             "(also reads HTTP_PROXY / HTTPS_PROXY env vars)")
    parser.add_argument("--no-validate",   action="store_true",
                        help="Skip stream validation, just merge all playlists")
    args = parser.parse_args()

    # ── install proxy / opener (must be first) ───────────────────────────
    install_proxy(args.proxy)

    # ── read playlist URLs ───────────────────────────────────────────────
    if not os.path.exists(args.input):
        log(f"Input file not found: {args.input}", "ERROR")
        sys.exit(1)

    with open(args.input, encoding="utf-8") as f:
        urls = [line.strip() for line in f
                if line.strip() and not line.strip().startswith("#")]

    if not urls:
        log("No URLs found in input file.", "ERROR")
        sys.exit(1)

    log(f"Found {len(urls)} playlist URL(s) in {args.input}")

    # ── download & parse all playlists ──────────────────────────────────
    all_channels: list[dict] = []
    for url in urls:
        channels = load_playlist(url, args.playlist_timeout)
        all_channels.extend(channels)

    if not all_channels:
        log("No channels parsed from any playlist.", "ERROR")
        sys.exit(1)

    log(f"Total channels to validate: {len(all_channels)}")

    if args.no_validate:
        write_m3u(all_channels, args.output)
        return

    # ── validate streams concurrently ───────────────────────────────────
    log(f"Validating with {args.workers} workers, timeout={args.timeout}s …")
    print()  # blank line before progress

    job_queue: Queue = Queue()
    for ch in all_channels:
        job_queue.put(ch)

    valid_channels: list[dict] = []
    lock = threading.Lock()
    counter = [0, len(all_channels)]   # [done, total]

    threads = []
    num_workers = min(args.workers, len(all_channels))
    for _ in range(num_workers):
        t = threading.Thread(
            target=worker,
            args=(job_queue, valid_channels, args.timeout, args.retry, lock, counter),
            daemon=True,
        )
        t.start()
        threads.append(t)

    for t in threads:
        t.join()

    print()  # end progress line
    print()

    total   = len(all_channels)
    valid   = len(valid_channels)
    invalid = total - valid
    pct     = valid / total * 100 if total else 0

    log(f"Results: {valid}/{total} valid ({pct:.1f}%)  |  {invalid} dead/unreachable")

    if valid_channels:
        write_m3u(valid_channels, args.output)
    else:
        log("No valid channels found — output file not written.", "WARN")


if __name__ == "__main__":
    main()
