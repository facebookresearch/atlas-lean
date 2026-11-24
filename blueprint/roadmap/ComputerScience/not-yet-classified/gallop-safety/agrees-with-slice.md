# Agrees With Slice

A direct source presents exactly the same logical keys as a reviewed
`SortSlice` call throughout the searched half-open range `[0, n)`.  The two
bases are intentionally independent: a temporary source can retain its real
physical offset while the materialized transcription slice starts at zero.
