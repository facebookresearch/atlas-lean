# Composition sum for a block of size $i$ inside a clade of size $j$

Let `n`, `k`, `i` and `j` be natural numbers with `k ≥ 2` and `j < n`.
Write `q(y, r)` for the number of compositions of `y` into `r` positive parts:
`q(0, 0) = 1`, `q(y, r) = C(y - 1, r - 1)` for `y, r ≥ 1`, and `q(y, r) = 0` if exactly one of
`y`, `r` is `0`. Let `a_m = q(j - i, m - 1)` if `i ≤ j` and `a_m = 0` otherwise. Then

`∑_{m=1}^{k-1} a_m q(n - j, k - m)` equals
`C(n - i - 1, k - 2) - C(n - i - 2, k - 2)` if `i < j`, `C(n - i - 1, k - 2)` if `i = j`, and `0`
if `i > j`.

All subtractions are nonnegative where they occur. It is the sum over the size `m` of a
sub-multiset of parts with sum `j` containing a part equal to `i`, in the
[sum over compositions of a part count times the clade statistic](sum-comps-count-mul-clade-stat.md).
