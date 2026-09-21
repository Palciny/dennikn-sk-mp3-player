from __future__ import annotations

import json
import os
import random
import re
import sys
import time
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from typing import Iterable
from urllib.parse import urljoin

import feedparser
import requests
from bs4 import BeautifulSoup

RSS_DIRECTORY_URL = "https://dennikn.sk/rss-odber/"
SITE_ROOT = "https://dennikn.sk/"
CDN_ROOT = "https://a-static.projektn.sk"

OUTPUT_PATH = Path(__file__).resolve().parents[1] / "docs" / "data" / "articles.json"
LATEST_OUTPUT_PATH = Path(__file__).resolve().parents[1] / "docs" / "data" / "latest.json"

MAX_FEED_ITEMS_PER_FEED = 150
REQUEST_TIMEOUT = 30

# Only brand-new articles are worth probing on the CDN. Audio normally appears
# within hours of publication, so anything older than this that we still do not
# have is treated as "no audio" instead of being re-probed on every run.
PROBE_MAX_AGE_DAYS = int(os.environ.get("PROBE_MAX_AGE_DAYS", "7"))

# Safety valve so a bad day cannot turn into tens of thousands of requests.
MAX_CDN_PROBES = int(os.environ.get("MAX_CDN_PROBES", "2500"))

# Fail the run if the newest article we know about is older than this.
MAX_STALE_DAYS = int(os.environ.get("MAX_STALE_DAYS", "3"))

# Suffixes ordered by how often they occur in the existing archive.
MP3_SUFFIXES = ["1", "2", "3", "4", "5", "6", "1-1", "1-2", "2-1"]

# Podcast RSS feeds, one URL per line in scripts/podcast_feeds.txt.
PODCAST_FEEDS_PATH = Path(__file__).resolve().parent / "podcast_feeds.txt"

# Recurring series use hand-made filenames keyed to the publication date rather
# than the post id. Verified against the existing archive: these recover a bit
# over half of the non-neural records. (title_prefix or None, filename template)
DATE_TEMPLATES = [
    ("Vývoj bojov", "exportVB{d}{m}{Y}.mp3"),
    ("Svetový newsfilter", "SNF{d}{m}{y}.mp3"),
    ("Svetový newsfilter", "SNF{d}{m}{Y}mixdown.mp3"),
    ("Newsfilter", "NF{d}{m}{y}.mp3"),
    ("Newsfilter", "NFF{d}{m}{y}.mp3"),
    ("Newsfilter", "NF{d}{m}{Y}mixdown.mp3"),
    ("Komentátori", "komentatori{d}{m}{Y}.mp3"),
    (None, "vredakcii{d}{m}{Y}.mp3"),
    (None, "dpoh{d}{m}{Y}.mp3"),
]

# Some series are dated the day before publication, so try a small window.
DATE_TEMPLATE_DAYS_BACK = (0, 1, 2)

MP3_RE = re.compile(r"https?://[^\s\"'<>]+\.mp3(?:\?[^\s\"'<>]*)?", re.IGNORECASE)
DENNIKN_ARTICLE_RE = re.compile(r"^https://dennikn\.sk/(\d+)/", re.IGNORECASE)
GUID_POST_ID_RE = re.compile(r"[?&]p=(\d+)")
CHALLENGE_MARKERS = (
    "cf-browser-verification",
    "just a moment",
    "challenge-platform",
    "attention required! | cloudflare",
)

KNOWN_FEEDS = [
    "https://dennikn.sk/feed",
    "https://dennikn.sk/slovensko/feed/",
    "https://dennikn.sk/svet/feed",
    "https://dennikn.sk/ekonomika/feed",
    "https://dennikn.sk/rodina-a-vztahy/feed",
    "https://dennikn.sk/zdravie/feed",
    "https://dennikn.sk/komentare/feed",
    "https://dennikn.sk/kultura/feed",
    "https://dennikn.sk/veda/feed",
    "https://dennikn.sk/sport/feed",
]

# A plain browser fingerprint. The old self-identifying bot UA is what most
# likely started getting filtered at the edge.
BROWSER_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"
    ),
    "Accept": (
        "text/html,application/xhtml+xml,application/xml;q=0.9,"
        "image/avif,image/webp,image/apng,*/*;q=0.8"
    ),
    "Accept-Language": "sk-SK,sk;q=0.9,cs;q=0.8,en-US;q=0.7,en;q=0.6",
    "Sec-Fetch-Dest": "document",
    "Sec-Fetch-Mode": "navigate",
    "Sec-Fetch-Site": "none",
    "Sec-Fetch-User": "?1",
    "Upgrade-Insecure-Requests": "1",
}


class BlockedError(RuntimeError):
    """The edge refused us (403/429) or served a challenge page."""


STATS = {
    "feeds_ok": 0,
    "feeds_failed": 0,
    "entries_seen": 0,
    "entries_known": 0,
    "entries_new": 0,
    "resolved_by_cdn": 0,
    "resolved_by_legacy": 0,
    "resolved_by_html": 0,
    "podcast_feeds_ok": 0,
    "podcast_feeds_failed": 0,
    "podcast_episodes_new": 0,
    "html_blocked": 0,
    "html_failed": 0,
    "cdn_probes": 0,
    "no_audio": 0,
    "too_old_to_probe": 0,
}


@dataclass
class ArticleRecord:
    title: str
    url: str
    mp3_url: str
    published: str | None
    published_day: str | None
    categories: list[str]
    feed_url: str | None
    first_seen: str
    last_seen: str


session = requests.Session()
session.headers.update(BROWSER_HEADERS)


def warm_up() -> None:
    """Pick up whatever cookies the edge wants to hand out before scraping."""
    try:
        response = session.get(SITE_ROOT, timeout=REQUEST_TIMEOUT)
        print(f"Warm-up GET {SITE_ROOT} -> {response.status_code}")
    except Exception as exc:
        print(f"Warm-up failed (continuing anyway): {exc}")


def fetch_text(url: str, *, referer: str | None = None, retries: int = 2) -> str:
    headers = {}
    if referer:
        headers["Referer"] = referer
        headers["Sec-Fetch-Site"] = "same-origin"

    last_exc: Exception | None = None
    for attempt in range(retries + 1):
        try:
            response = session.get(url, timeout=REQUEST_TIMEOUT, headers=headers)
            if response.status_code in (403, 429, 503):
                raise BlockedError(f"HTTP {response.status_code}")
            response.raise_for_status()
            body = response.text
            head = body[:4000].lower()
            if any(marker in head for marker in CHALLENGE_MARKERS):
                raise BlockedError("interstitial challenge page")
            return body
        except Exception as exc:
            last_exc = exc
            if attempt < retries:
                time.sleep(2 ** attempt + random.random())
    raise last_exc if last_exc else RuntimeError("unreachable")


def url_exists(url: str) -> bool:
    """HEAD the CDN, falling back to a one-byte ranged GET."""
    STATS["cdn_probes"] += 1
    try:
        response = session.head(url, timeout=REQUEST_TIMEOUT, allow_redirects=True)
        if response.status_code in (403, 405, 501):
            response = session.get(
                url,
                timeout=REQUEST_TIMEOUT,
                allow_redirects=True,
                headers={"Range": "bytes=0-0"},
            )
        return response.status_code in (200, 206)
    except Exception as exc:
        print(f"  probe error {url}: {exc}")
        return False


def parse_published(value: str | None) -> str | None:
    if not value:
        return None
    try:
        dt = parsedate_to_datetime(value)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc).isoformat()
    except Exception:
        return None


def iso_day(value: str | None) -> str | None:
    if not value:
        return None
    return value[:10]


def dedupe_keep_order(values: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for value in values:
        value = (value or "").strip()
        if not value or value in seen:
            continue
        seen.add(value)
        result.append(value)
    return result


def discover_feed_urls() -> list[str]:
    discovered: list[str] = []
    try:
        html = fetch_text(RSS_DIRECTORY_URL)
        soup = BeautifulSoup(html, "html.parser")
        for link in soup.select("a[href]"):
            href = (link.get("href") or "").strip()
            text = " ".join(link.stripped_strings)
            if "/feed" not in href:
                continue
            if "Minúty" in text or "Minúta" in text:
                continue
            discovered.append(urljoin(RSS_DIRECTORY_URL, href))
    except Exception as exc:
        print(f"Could not discover feeds from {RSS_DIRECTORY_URL}: {exc}")

    return dedupe_keep_order([*discovered, *KNOWN_FEEDS])


def post_id_from_entry(entry, url: str) -> str | None:
    match = DENNIKN_ARTICLE_RE.match(url)
    if match:
        return match.group(1)
    guid = (entry.get("id") or entry.get("guid") or "") if hasattr(entry, "get") else ""
    match = GUID_POST_ID_RE.search(guid or "")
    return match.group(1) if match else None


def month_candidates(published_iso: str | None) -> list[str]:
    """`YYYY/MM` folders to try, publish month first."""
    if published_iso:
        try:
            base = datetime.fromisoformat(published_iso)
        except ValueError:
            base = datetime.now(timezone.utc)
    else:
        base = datetime.now(timezone.utc)

    first_of_month = base.replace(day=1)
    previous = first_of_month - timedelta(days=1)
    following = (first_of_month + timedelta(days=32)).replace(day=1)
    return dedupe_keep_order(
        [d.strftime("%Y/%m") for d in (base, previous, following)]
    )


def derive_mp3_url(post_id: str, published_iso: str | None) -> str | None:
    """
    The neural-audio files are named deterministically:
        https://a-static.projektn.sk/<YYYY>/<MM>/neural-audio-elevenlabs-<post_id>-<n>.mp3
    Verified against every record in the existing archive. Probing the CDN
    directly avoids fetching the article page at all.
    """
    for folder in month_candidates(published_iso):
        for suffix in MP3_SUFFIXES:
            if STATS["cdn_probes"] >= MAX_CDN_PROBES:
                print("CDN probe budget exhausted")
                return None
            candidate = f"{CDN_ROOT}/{folder}/neural-audio-elevenlabs-{post_id}-{suffix}.mp3"
            if url_exists(candidate):
                return candidate
    return None


def derive_legacy_mp3_url(title: str, published_iso: str | None) -> str | None:
    """Probe the date-keyed filenames used by the recurring series."""
    if not published_iso:
        return None
    try:
        base = datetime.fromisoformat(published_iso)
    except ValueError:
        return None

    name = (title or "").casefold()
    for days_back in DATE_TEMPLATE_DAYS_BACK:
        day = base - timedelta(days=days_back)
        parts = {
            "d": f"{day.day:02d}",
            "m": f"{day.month:02d}",
            "Y": str(day.year),
            "y": f"{day.year % 100:02d}",
        }
        folder = day.strftime("%Y/%m")
        for prefix, template in DATE_TEMPLATES:
            if prefix and not name.startswith(prefix.casefold()):
                continue
            if STATS["cdn_probes"] >= MAX_CDN_PROBES:
                print("CDN probe budget exhausted")
                return None
            candidate = f"{CDN_ROOT}/{folder}/{template.format(**parts)}"
            if url_exists(candidate):
                return candidate
    return None


def extract_main_mp3(html: str, page_url: str) -> str | None:
    soup = BeautifulSoup(html, "html.parser")

    for source in soup.select("audio source[src]"):
        src = source.get("src", "").strip()
        if src and src.lower().endswith(".mp3") and "predplatne.mp3" not in src.lower():
            return urljoin(page_url, src)

    for audio in soup.select("audio[src]"):
        src = audio.get("src", "").strip()
        if src and src.lower().endswith(".mp3") and "predplatne.mp3" not in src.lower():
            return urljoin(page_url, src)

    for match in MP3_RE.findall(html):
        if "predplatne.mp3" in match.lower():
            continue
        return match

    return None


def extract_categories(entry, html: str | None) -> list[str]:
    categories: list[str] = []

    for tag in entry.get("tags", []) or []:
        term = (getattr(tag, "term", None) or tag.get("term") or "").strip()
        if term:
            categories.append(term)

    if categories or not html:
        return dedupe_keep_order(categories)

    soup = BeautifulSoup(html, "html.parser")
    selector = (
        'meta[property="article:tag"], meta[name="news_keywords"], '
        'meta[property="article:section"]'
    )
    for meta in soup.select(selector):
        content = (meta.get("content") or "").strip()
        if not content:
            continue
        for part in [x.strip() for x in content.split(",")]:
            if part:
                categories.append(part)

    return dedupe_keep_order(categories)


def iter_feed_entries():
    for feed_url in discover_feed_urls():
        try:
            parsed = feedparser.parse(fetch_text(feed_url))
            STATS["feeds_ok"] += 1
        except Exception as exc:
            STATS["feeds_failed"] += 1
            print(f"Skipping feed {feed_url}: {exc}")
            continue

        for entry in parsed.entries[:MAX_FEED_ITEMS_PER_FEED]:
            link = (entry.get("link") or "").strip()
            if not link or not DENNIKN_ARTICLE_RE.search(link):
                continue
            yield feed_url, entry


def load_podcast_feeds() -> list[str]:
    if not PODCAST_FEEDS_PATH.exists():
        return []
    lines = PODCAST_FEEDS_PATH.read_text(encoding="utf-8").splitlines()
    return dedupe_keep_order(
        line.strip() for line in lines if line.strip() and not line.startswith("#")
    )


def episode_audio_url(entry) -> str | None:
    """Pull the MP3 out of a podcast entry's enclosure or media content."""
    for link in entry.get("links", []) or []:
        href = (link.get("href") or "").strip()
        rel = link.get("rel") or ""
        mime = link.get("type") or ""
        if rel == "enclosure" and href and ("audio" in mime or ".mp3" in href.lower()):
            return href

    for media in entry.get("media_content", []) or []:
        href = (media.get("url") or "").strip()
        if href and ".mp3" in href.lower():
            return href

    return None


def ingest_podcasts(
    records_by_url: dict[str, ArticleRecord],
    seen_mp3s: set[str],
    now_iso: str,
) -> list[str]:
    """Podcast episodes come straight from their own RSS - no scraping needed."""
    feeds_used: list[str] = []

    for feed_url in load_podcast_feeds():
        try:
            parsed = feedparser.parse(fetch_text(feed_url))
            STATS["podcast_feeds_ok"] += 1
        except Exception as exc:
            STATS["podcast_feeds_failed"] += 1
            print(f"Skipping podcast feed {feed_url}: {exc}")
            continue

        show = (parsed.feed.get("title") or "").strip()
        feeds_used.append(feed_url)

        for entry in parsed.entries[:MAX_FEED_ITEMS_PER_FEED]:
            mp3_url = episode_audio_url(entry)
            if not mp3_url or mp3_url in seen_mp3s:
                continue

            page_url = (entry.get("link") or "").strip() or mp3_url
            if page_url in records_by_url:
                records_by_url[page_url].last_seen = now_iso
                continue

            published = parse_published(entry.get("published") or entry.get("updated"))
            title = (entry.get("title") or page_url).strip()
            categories = dedupe_keep_order([show] if show else [])

            records_by_url[page_url] = ArticleRecord(
                title=title,
                url=page_url,
                mp3_url=mp3_url,
                published=published,
                published_day=iso_day(published),
                categories=categories,
                feed_url=feed_url,
                first_seen=now_iso,
                last_seen=now_iso,
            )
            seen_mp3s.add(mp3_url)
            STATS["podcast_episodes_new"] += 1
            print(f"  + [podcast] {title[:60]} -> {mp3_url}")

    return feeds_used


def load_existing_records(now_iso: str) -> dict[str, ArticleRecord]:
    if not OUTPUT_PATH.exists():
        return {}

    try:
        payload = json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"Could not read existing archive: {exc}")
        return {}

    existing: dict[str, ArticleRecord] = {}
    for item in payload.get("articles", []) or []:
        url = (item.get("url") or "").strip()
        mp3_url = (item.get("mp3_url") or "").strip()
        if not url or not mp3_url:
            continue
        existing[url] = ArticleRecord(
            title=(item.get("title") or url).strip(),
            url=url,
            mp3_url=mp3_url,
            published=item.get("published"),
            published_day=item.get("published_day") or iso_day(item.get("published")),
            categories=dedupe_keep_order(item.get("categories") or []),
            feed_url=item.get("feed_url"),
            first_seen=item.get("first_seen") or now_iso,
            last_seen=item.get("last_seen") or now_iso,
        )
    return existing


def resolve_mp3(url: str, post_id: str | None, published: str | None, title: str = ""):
    """Returns (mp3_url, article_html). CDN first, article page as fallback."""
    if post_id:
        mp3_url = derive_mp3_url(post_id, published)
        if mp3_url:
            STATS["resolved_by_cdn"] += 1
            return mp3_url, None

    mp3_url = derive_legacy_mp3_url(title, published)
    if mp3_url:
        STATS["resolved_by_legacy"] += 1
        return mp3_url, None

    # Older, hand-recorded audio does not follow the neural-audio naming, so we
    # still try the article page. This is the path that the edge may block.
    try:
        html = fetch_text(url, referer=SITE_ROOT)
    except BlockedError as exc:
        STATS["html_blocked"] += 1
        print(f"  blocked fetching {url}: {exc}")
        return None, None
    except Exception as exc:
        STATS["html_failed"] += 1
        print(f"  failed fetching {url}: {exc}")
        return None, None

    mp3_url = extract_main_mp3(html, url)
    if mp3_url:
        STATS["resolved_by_html"] += 1
    return mp3_url, html


def build_records() -> tuple[list[ArticleRecord], list[str]]:
    now = datetime.now(timezone.utc)
    now_iso = now.isoformat()
    existing = load_existing_records(now_iso)
    records_by_url = dict(existing)
    seen_mp3s = {record.mp3_url for record in records_by_url.values()}
    probe_cutoff = now - timedelta(days=PROBE_MAX_AGE_DAYS)

    feed_urls_seen: list[str] = []

    for feed_url, entry in iter_feed_entries():
        feed_urls_seen.append(feed_url)
        STATS["entries_seen"] += 1

        url = (entry.get("link") or "").strip()
        title = (entry.get("title") or url).strip()
        published = parse_published(entry.get("published") or entry.get("updated"))

        previous = records_by_url.get(url)
        if previous is not None:
            # Already have the audio; just refresh last_seen and move on.
            STATS["entries_known"] += 1
            previous.last_seen = now_iso
            continue

        # Audio shows up within hours of publication. If we still do not have an
        # old article, it simply has no audio version - do not probe it forever.
        if published:
            try:
                if datetime.fromisoformat(published) < probe_cutoff:
                    STATS["too_old_to_probe"] += 1
                    continue
            except ValueError:
                pass

        STATS["entries_new"] += 1
        post_id = post_id_from_entry(entry, url)
        mp3_url, html = resolve_mp3(url, post_id, published, title)

        if not mp3_url:
            STATS["no_audio"] += 1
            continue

        if mp3_url in seen_mp3s:
            continue

        record = ArticleRecord(
            title=title,
            url=url,
            mp3_url=mp3_url,
            published=published,
            published_day=iso_day(published),
            categories=extract_categories(entry, html),
            feed_url=feed_url,
            first_seen=now_iso,
            last_seen=now_iso,
        )
        records_by_url[url] = record
        seen_mp3s.add(mp3_url)
        print(f"  + {title[:70]} -> {mp3_url}")

    feed_urls_seen.extend(ingest_podcasts(records_by_url, seen_mp3s, now_iso))

    records = list(records_by_url.values())
    records.sort(
        key=lambda item: (
            item.published or "",
            item.first_seen,
            item.title.lower(),
        ),
        reverse=True,
    )
    return records, dedupe_keep_order(feed_urls_seen)


def build_payload(
    *,
    records: list[ArticleRecord],
    payload_records: list[ArticleRecord],
    feed_urls: list[str],
    generated_at: str,
    latest_day: str | None,
) -> dict:
    categories = sorted(
        {category for record in records for category in record.categories},
        key=str.casefold,
    )
    published_days = sorted(
        {record.published_day for record in records if record.published_day},
        reverse=True,
    )
    return {
        "generated_at": generated_at,
        "sources": feed_urls,
        "count": len(payload_records),
        "total_count": len(records),
        "latest_day": latest_day,
        "categories": categories,
        "published_days": published_days,
        "articles": [asdict(record) for record in payload_records],
    }


def write_output(records: list[ArticleRecord], feed_urls: list[str]) -> str | None:
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    published_days = sorted(
        {record.published_day for record in records if record.published_day},
        reverse=True,
    )
    latest_day = published_days[0] if published_days else None
    latest_records = [
        record
        for record in records
        if latest_day is None or record.published_day == latest_day
    ]
    generated_at = datetime.now(timezone.utc).isoformat()
    payload = build_payload(
        records=records,
        payload_records=records,
        feed_urls=feed_urls,
        generated_at=generated_at,
        latest_day=latest_day,
    )
    latest_payload = build_payload(
        records=records,
        payload_records=latest_records,
        feed_urls=feed_urls,
        generated_at=generated_at,
        latest_day=latest_day,
    )

    OUTPUT_PATH.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    LATEST_OUTPUT_PATH.write_text(
        json.dumps(latest_payload, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    return latest_day


def health_check(latest_day: str | None) -> int:
    """Return a non-zero exit code when the run looks broken rather than idle."""
    problems: list[str] = []

    if STATS["feeds_ok"] == 0:
        problems.append("no RSS feed could be read at all")

    if STATS["entries_new"] > 0:
        blocked = STATS["html_blocked"]
        if blocked and blocked >= STATS["entries_new"]:
            problems.append(f"every article fetch was blocked ({blocked})")

    if latest_day:
        try:
            age = (datetime.now(timezone.utc).date() - datetime.strptime(latest_day, "%Y-%m-%d").date()).days
            if age > MAX_STALE_DAYS:
                problems.append(f"newest article is {age} days old (limit {MAX_STALE_DAYS})")
        except ValueError:
            pass
    else:
        problems.append("no articles in the index")

    if not problems:
        return 0

    print("\n::error::Build looks broken, not just quiet:")
    for problem in problems:
        print(f"::error::  - {problem}")
    return 1


if __name__ == "__main__":
    warm_up()
    items, feed_urls = build_records()
    latest_day = write_output(items, feed_urls)

    print("\n--- run summary ---")
    for key, value in STATS.items():
        print(f"{key:>20}: {value}")
    print(f"{'total_records':>20}: {len(items)}")
    print(f"{'latest_day':>20}: {latest_day}")
    print(f"Wrote {OUTPUT_PATH} and {LATEST_OUTPUT_PATH}")

    sys.exit(health_check(latest_day))
