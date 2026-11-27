# The polynomial map gives the f2 values of the admixture drift model

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on the counting measure of a
four-point set `Ω`, with four edges and three populations `A = 0`, `B = 1`, `C = 2`, whose lineage
weights are the [weights of the four-edge admixture graph](three-pop-weights.md) for some real `α`
and whose drift lengths are `(s, a, b, c)` on the stem, `A`, `B` and `C` edges. Then the
[polynomial f2 map](three-pop-f2.md) at `(α, s, a, b, c)` is the vector of the
[f2 statistics](../patterson-s-f-statistics/f2.md) of its
[population frequencies](../patterson-s-f-statistics/freq.md):
`(a + b, (1 - α) ^ 2 * (a + b) + c, α ^ 2 * (a + b) + c) = (f2(A, B), f2(A, C), f2(B, C))`. Drift
lengths are [nonnegative](../patterson-s-f-statistics/len-nonneg.md), and for every `α` and all
`s, a, b, c ≥ 0` such a model exists: identify the four points of `Ω` with the four edges and take
the increment of edge `e` equal to `√ℓ_e` at the point `e` and `0` elsewhere, where `ℓ_e` is the
length of `e`.
