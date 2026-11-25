# A square injective truss equilibrium matrix gives one balance per load

Consider a planar pin-jointed truss with finitely many joints `J` at positions `r_j ∈ ℝ²`, members
`M` joining the joints `a(e)` and `b(e)`, and support reactions `R` at the joints `sj(s)` along the
directions `sd(s) ∈ ℝ²`. Suppose `|M| + |R| = 2 |J|` and the
[equilibrium matrix](../../../elasticity-and-structures/truss-equilibrium-load-envelopes-and-load-infere/equilibrium-matrix.md)
`A` is injective as a linear map on `ℝ^{M ⊔ R}`. Then every joint load `f ∈ ℝ^{J × {0, 1}}` has
exactly one pair of member forces `N` and reactions `ρ` in
[joint balance](../../../elasticity-and-structures/truss-equilibrium-load-envelopes-and-load-infere/joint-balance.md)
with `f`.
