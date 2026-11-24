# Closed form of the composition sum inside a clade of size $j$

Let `n`, `k`, `i` and `j` be natural numbers with `k ≥ 2` and `j < n`; no bound on `k` relative
to `n` is assumed, and binomial coefficients are extended by `C(u, v) = 0` for natural `v > u`.
Write `q(y, r)` for the number of compositions of `y` into `r` positive parts:
`q(0, 0) = 1`, `q(y, r) = C(y - 1, r - 1)` for `y, r ≥ 1`, and `q(y, r) = 0` if exactly one of
`y`, `r` is `0`. Let `a_m = q(j - i, m - 1)` if `i ≤ j` and `a_m = 0` otherwise. Then

`∑_{m=1}^{k-1} a_m q(n - j, k - m)` equals
`C(n - i - 1, k - 2) - C(n - i - 2, k - 2)` if `i < j`, `C(n - i - 1, k - 2)` if `i = j`, and `0`
if `i > j`.

All subtractions are nonnegative where they occur. The identity is algebraic and holds for every
`i`, including `i = 0`. For `i ≥ 1` it is the sum over the size `m` of a sub-multiset of parts
with sum `j` containing a part equal to `i`, in the
[sum over compositions of a part count times the clade statistic](sum-comps-count-mul-clade-stat.md).
For `i = 0` no part has size `0`, and the sum has no such reading (for `n = 3`, `k = 2` and
`j = 0` it equals `1`).
