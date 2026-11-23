# Equal mixed drift gives equal f2 between the admixed and a reference

Let `M` and `M'` be [drift models](../patterson-s-f-statistics/drift-model.md) with the same
populations and edges, possibly on different measure spaces, with the same lineage weights `w` and
with drift lengths `ℓ` and `ℓ'`. Let `a, b, c` be distinct edges, `α` a real number, and
`Mx, A, B, X` populations such that `w(Mx, ·) = α (w(A, ·) + 1_a) + (1 - α) (w(B, ·) + 1_b) + 1_c`,
where `1_e` is the indicator of edge `e` (`Mx` is an `α : 1 - α` mixture of the lower ends of an
edge `a` below `A` and an edge `b` below `B`, followed by drift along `c`), and `A`, `B` and `X`
have weight `0` on `a`, `b` and `c`. If `ℓ'(e) = ℓ(e)` for every edge `e` other than `a, b, c` and
the [mixed drifts](../outgroup-f3-and-admixed-branches/mixed-drift.md) agree,
`α² ℓ'_a + (1 - α)² ℓ'_b + ℓ'_c = α² ℓ_a + (1 - α)² ℓ_b + ℓ_c`, then the two models give the same
value of the [f2 statistic](../patterson-s-f-statistics/f2.md) `f2(Mx, X)`. So these f2 statistics
do not separate the three lengths `ℓ_a, ℓ_b, ℓ_c`; they see them only through the mixed drift.
