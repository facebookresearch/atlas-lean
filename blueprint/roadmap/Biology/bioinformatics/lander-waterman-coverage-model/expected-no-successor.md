# Expected number of no-successor reads (exact)

For `0 < G` and `L ≤ G`, the
expected number of reads with no successor is `N (1 - (L - 1) / G) ^ (N - 1)`.
The `0 < G` hypothesis is essential: at `G = 0` and `N > 0`, the right-hand expression is
`N` while the sum of totalized normalized counts is zero.
