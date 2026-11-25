# Full column rank: equal f4 statistics give equal edge lengths

Let `w(X, e)` be lineage weights of populations `X` on a finite set of edges `e`, and let
`(A_i, B_i, C_i, D_i)`, for `i` in an arbitrary index set, be quadruples of populations with
[design matrix](../fitting-admixture-graphs-by-least-squares/design-matrix.md) `B`,
`B_ie = (w(A_i, e) - w(B_i, e)) (w(C_i, e) - w(D_i, e))`. Suppose that `B` has full column rank,
that is, the linear map `ℓ ↦ B ℓ` is injective. If two
[drift models](../patterson-s-f-statistics/drift-model.md), possibly on different measure spaces,
both have lineage weights `w` and give the same value of the
[f4 statistic](../patterson-s-f-statistics/f4.md) `f4(A_i, B_i; C_i, D_i)` of their population
frequencies for every `i`, then they have the same drift lengths: `ℓ(e) = ℓ'(e)` for every edge `e`.
