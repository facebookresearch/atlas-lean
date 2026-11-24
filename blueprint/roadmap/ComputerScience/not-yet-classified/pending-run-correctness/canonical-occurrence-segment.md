# Canonical Occurrence Segment

Canonical tags for exactly `[base, base + scanned)` in the original input.

Tagging happens before extraction, so every retained origin is an absolute
index in `input`, rather than an index manufactured relative to this segment.
No element beyond the selected segment occurs in this definition.
