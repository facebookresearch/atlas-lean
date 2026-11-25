# The level moment as an average over compositions

For natural numbers `n`, `k`, `i` and `j` with `2 ≤ k ≤ n`,

`M_n(k; i, j) C(n - 1, k - 1) = ∑_c c_i(c) S_k(1_j, P(c))`,

where `M_n(k; i, j)` is the [level moment](level-moment.md), `c` runs over the compositions of `n`
into `k` positive parts, `P(c)` is the multiset of the parts of `c` and `c_i(c)` the number of parts
equal to `i`, and `S_k(1_j, P(c)) = ∑_s w_k(|s|)` over the sub-multisets `s` of `P(c)` (one for each
set of positions) with sum `j` is the [clade statistic](clade-stat.md) of the
[indicator of the size `j`](size-ind.md), with `w_k(m) = 2 / (m C(k, m))` for `1 ≤ m < k` and `0`
otherwise. Since there are `C(n - 1, k - 1)` such compositions, the level moment is the average of
`c_i(c) S_k(1_j, P(c))` over a uniformly chosen composition of `n` into `k` positive parts.
