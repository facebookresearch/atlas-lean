# Sum over compositions of a part count times the clade statistic

Let `n`, `k`, `i` and `j` be natural numbers with `i ≥ 1` and `j ≤ n`.
Write `q(y, r)` for the number of compositions of `y` into `r` positive parts:
`q(0, 0) = 1`, `q(y, r) = C(y - 1, r - 1)` for `y, r ≥ 1`, and `q(y, r) = 0` if exactly one of
`y`, `r` is `0`. Let `w_k(m) = 2 / (m C(k, m))` for `1 ≤ m < k` and `w_k(m) = 0`
otherwise.
For a composition `c` of `n` into `k` positive parts, let `P(c)` be the multiset of its parts
and `c_i(c)` the number of parts equal to `i`. Then, summing over these compositions,

`∑_c c_i(c) S_k(1_j, P(c)) = ∑_{m=0}^{k} w_k(m) C(k, m) T_m`, with
`T_m = m a_m q(n - j, k - m) + (k - m) q(j, m) b_m`,

where `S_k(1_j, P(c)) = ∑_s w_k(|s|)` over the sub-multisets `s` of `P(c)` (one for each set of
positions) with sum `j` is the [clade statistic](clade-stat.md) of the
[indicator of the size `j`](size-ind.md), `a_m = q(j - i, m - 1)` if `i ≤ j` and `a_m = 0`
otherwise, and `b_m = q(n - j - i, k - m - 1)` if `i ≤ n - j` and `b_m = 0` otherwise. The
subtractions `m - 1` and `k - m - 1` are truncated at `0` only in terms multiplied by `m = 0` or
`k - m = 0`. The first term of `T_m` counts the parts equal to `i` inside a sub-multiset of sum
`j`, the second those outside it.
