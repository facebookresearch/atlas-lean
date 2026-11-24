# f4 is unchanged by a common signed shift of the lineage weights

Let `M` and `M'` be [drift models](../patterson-s-f-statistics/drift-model.md) with the same
populations and edges, possibly on different measure spaces, with the same drift lengths. Suppose
that there are real numbers `s(e) ∈ {1, -1}` and `c(e)`, one pair for each edge `e`, such that the
lineage weights satisfy `w'(X, e) = s(e) w(X, e) + c(e)` for every population `X` and every edge
`e`. Then the two models give the same value of the
[f4 statistic](../patterson-s-f-statistics/f4.md) `f4(A, B; C, D)` for all populations `A, B, C, D`:
f4 statistics do not distinguish weight vectors that differ by such a common signed shift.
