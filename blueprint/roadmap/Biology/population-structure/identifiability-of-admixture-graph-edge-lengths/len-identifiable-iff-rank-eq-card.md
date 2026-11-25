# Rank criterion for the identifiability of edge lengths

Let `w(X, e)` be lineage weights of populations `X` on a finite set `E` of edges, and let
`(A_i, B_i, C_i, D_i)`, for `i` in an arbitrary index set, be quadruples of populations with
[design matrix](../fitting-admixture-graphs-by-least-squares/design-matrix.md) `B`,
`B_ie = (w(A_i, e) - w(B_i, e)) (w(C_i, e) - w(D_i, e))`. Consider the
[drift models](../patterson-s-f-statistics/drift-model.md) on the counting measure of `E` (each edge
a point, every subset measurable) with lineage weights `w`. Any two of them that give the same value
of the [f4 statistic](../patterson-s-f-statistics/f4.md) `f4(A_i, B_i; C_i, D_i)` for every `i` have
the same drift lengths if and only if `B` has rank equal to the number of edges, `rank B = |E|`
(full column rank). Full column rank gives the same conclusion for drift models on arbitrary measure
spaces ([equal f4 statistics give equal edge lengths](len-eq-of-f4-eq.md)).
