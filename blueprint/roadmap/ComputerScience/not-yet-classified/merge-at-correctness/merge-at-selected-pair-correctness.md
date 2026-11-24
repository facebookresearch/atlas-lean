# Merge At Selected Pair Correctness

Functional certificate for the exact pair selected by `merge_at`.

`exactRange` covers the complete pre-trimming union, not merely the smaller
middle range passed to `merge_lo` or `merge_hi`.  Thus the unchanged galloped
prefix and suffix are part of the observable result.
