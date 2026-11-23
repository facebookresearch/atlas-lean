# Composition sum for a block of size $i$ outside a clade of size $j$

Let `n`, `k`, `i` and `j` be natural numbers with `k ≥ 2` and `1 ≤ j < n`.
Write `q(y, r)` for the number of compositions of `y` into `r` positive parts:
`q(0, 0) = 1`, `q(y, r) = C(y - 1, r - 1)` for `y, r ≥ 1`, and `q(y, r) = 0` if exactly one of
`y`, `r` is `0`. Let `b_m = q(n - j - i, k - m - 1)` if `i ≤ n - j` and `b_m = 0` otherwise. Then

`∑_{m=1}^{k-1} (1/m) q(j, m) (k - m) b_m`

equals `E / j` if `i + j < n`, `C(j, k - 1) / j` if `i + j = n`, and `0` if `i + j > n`, where

`E = (n - i - j - 1) (C(n - i - 1, k - 2) - C(n - i - 2, k - 2)) + R`, with
`R = 2 C(n - i - 1, k - 2) - k C(n - i - j - 1, k - 2)`.

All subtractions are nonnegative where they occur. It is the sum over the size `m` of a
sub-multiset of parts with sum `j`, the part equal to `i` lying outside it, in the
[sum over compositions of a part count times the clade statistic](sum-comps-count-mul-clade-stat.md).
