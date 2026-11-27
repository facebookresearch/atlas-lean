# Without full column rank, edge lengths are not identifiable

Let `w(X, e)` be lineage weights of populations `X` on a finite set `E` of edges, and let
`(A_i, B_i, C_i, D_i)`, for `i` in an arbitrary index set, be quadruples of populations whose
[design matrix](../fitting-admixture-graphs-by-least-squares/design-matrix.md) `B`,
`B_ie = (w(A_i, e) - w(B_i, e)) (w(C_i, e) - w(D_i, e))`, does not have full column rank: `B v = 0`
for some nonzero vector `v`, that is, the linear map `ℓ ↦ B ℓ` is not injective. Then there are two
[drift models](../patterson-s-f-statistics/drift-model.md) on the counting measure of `E` (each edge
a point, every subset measurable), both with lineage weights `w`, with different drift-length
vectors, and giving the same value of the [f4 statistic](../patterson-s-f-statistics/f4.md)
`f4(A_i, B_i; C_i, D_i)` of their population frequencies for every `i`.
