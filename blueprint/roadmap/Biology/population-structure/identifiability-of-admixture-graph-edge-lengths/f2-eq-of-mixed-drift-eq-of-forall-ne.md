# Equal mixed drift gives the same f2 for all pairs of populations

Let `M` and `M'` be [drift models](../patterson-s-f-statistics/drift-model.md) with the same
populations and edges, possibly on different measure spaces, with the same lineage weights `w` and
with drift lengths `ℓ` and `ℓ'`. Let `a, b, c` be distinct edges, `α` a real number, and `Mx, A, B`
populations such that `w(Mx, ·) = α (w(A, ·) + 1_a) + (1 - α) (w(B, ·) + 1_b) + 1_c`, where `1_e` is
the indicator of edge `e`, and such that `A`, `B` and every population other than `Mx` have weight
`0` on `a`, `b` and `c`. If `ℓ'(e) = ℓ(e)` for every edge `e` other than `a, b, c` and the
[mixed drifts](../outgroup-f3-and-admixed-branches/mixed-drift.md) agree,
`α² ℓ'_a + (1 - α)² ℓ'_b + ℓ'_c = α² ℓ_a + (1 - α)² ℓ_b + ℓ_c`, then the two models give the same
value of the [f2 statistic](../patterson-s-f-statistics/f2.md) `f2(Y, Z)` for all populations
`Y, Z`.
