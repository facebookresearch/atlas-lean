# Cross-diagonal dependence coefficient of order k

For real weights `p` and `q` on a finite alphabet, a real score `s` on pairs of letters, natural
numbers `m` and `n`, a real `t` and a natural number `k`, the cross-diagonal dependence
coefficient is `Δ_k = S_k - e_k(p_·)`, where `S_k` is the
[exceedance moment](exceed-moment.md) of order `k` and `e_k(p_·)` the
[elementary symmetric sum](elem-symm.md) of the [exceedance probabilities](exceed-prob.md) `p_d`
over the [offsets](offsets.md) `-m < d < n`. When `p` and `q` are probability vectors, `e_k(p_·)`
is the value `S_k` would have for independent diagonals with the same exceedance probabilities, so
`Δ_k` measures the dependence between diagonals. It is the
[sum over the sets of `k` offsets](cross-dep-eq-sum.md) `T` of
`P(every diagonal in T exceeds t) - ∏_{d ∈ T} p_d`. Always `Δ_1 = 0`; when `p` and `q` are
probability vectors also `Δ_0 = 0`, and the term of a pair of diagonals that
[read disjoint sets of letters](two-prob-diag-and-diag-of-disjoint.md) is `0`. Diagonals that
share letters need not be independent, so for `k ≥ 2` the coefficient need not vanish.
