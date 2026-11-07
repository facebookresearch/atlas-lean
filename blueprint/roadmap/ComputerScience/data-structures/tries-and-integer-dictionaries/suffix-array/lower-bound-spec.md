# Binary search is correct

If `p` holds on an initial segment of `[lo, hi)` (whenever it
holds at `j`, it holds at every `i` with `lo ≤ i ≤ j`), then `lowerBound p lo hi` is the end `k` of
that segment: `lo ≤ k ≤ hi`, `p` holds on `[lo, k)` and fails on `[k, hi)`.
