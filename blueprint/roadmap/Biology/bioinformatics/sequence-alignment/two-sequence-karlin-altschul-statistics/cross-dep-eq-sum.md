# The dependence coefficient as a sum of joint-minus-product terms

For real weights `p` and `q` on a finite alphabet, a real score `s` on pairs of letters, natural
numbers `m` and `n`, a real `t` and a natural number `k`, the
[cross-diagonal dependence coefficient](cross-dep.md) is
`Δ_k = ∑_T (P(M_d > t for every d ∈ T) - ∏_{d ∈ T} p_d)`, the sum over the sets `T` of `k`
[offsets](offsets.md) `-m < d < n`. Here `P` is the [two-sequence probability](two-prob.md) over
words of lengths `m` and `n`, `M_d` is the maximal segment score of the
[diagonal of offset](diag.md) `d` and `p_d` is the [exceedance probability](exceed-prob.md).
