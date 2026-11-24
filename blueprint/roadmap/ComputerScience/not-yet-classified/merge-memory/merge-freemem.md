# Merge Freemem

Transcription of `merge_freemem`. Inline storage is retained. Any
non-inline key storage is released and its allocated cells cease to be
accessible; `alloced` and `hasValues` are intentionally unchanged.
