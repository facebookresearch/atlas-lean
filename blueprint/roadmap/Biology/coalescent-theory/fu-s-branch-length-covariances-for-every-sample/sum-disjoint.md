# Closed form of the composition sum outside a clade of size $j$

Let `n`, `k`, `i` and `j` be natural numbers with `k ≥ 2` and `1 ≤ j < n`; no bound on `k`
relative to `n` is assumed, and binomial coefficients are extended by `C(u, v) = 0` for natural
`v > u`. Write `q(y, r)` for the number of compositions of `y` into `r` positive parts:
`q(0, 0) = 1`, `q(y, r) = C(y - 1, r - 1)` for `y, r ≥ 1`, and `q(y, r) = 0` if exactly one of
`y`, `r` is `0`. Let `b_m = q(n - j - i, k - m - 1)` if `i ≤ n - j` and `b_m = 0` otherwise. Then

`∑_{m=1}^{k-1} (1/m) q(j, m) (k - m) b_m`

equals `E / j` if `i + j < n`, `C(j, k - 1) / j` if `i + j = n`, and `0` if `i + j > n`, where

`E = (n - i - j - 1) (C(n - i - 1, k - 2) - C(n - i - 2, k - 2)) + R`, with
`R = 2 C(n - i - 1, k - 2) - k C(n - i - j - 1, k - 2)`.

No subtraction of natural numbers goes below `0` where it occurs; the differences in `E` and
`R` are ordinary differences of real numbers, and `R` can be negative: for
`(n, k, i, j) = (10, 3, 1, 1)`, `R = 16 - 21 = -5`.

The identity is algebraic and holds for every `i`, including `i = 0`. For `i ≥ 1` it is the sum
over the size `m` of a sub-multiset of parts with sum `j`, a part equal to `i` lying outside it,
in the [sum over compositions of a part count times the clade statistic](sum-comps-count-mul-clade-stat.md).
For `i = 0` no part has size `0`, and the sum has no such reading (for `n = k = 3` and `j = 1` it
equals `2`).
