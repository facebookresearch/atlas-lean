# A truss load has a balance exactly when the ranks agree

Consider a planar pin-jointed truss with finitely many joints `J` at positions `r_j ∈ ℝ²`, finitely
many members `M` joining the joints `a(e)` and `b(e)`, and finitely many support reactions `R` at
the joints `sj(s)` along the directions `sd(s) ∈ ℝ²`. A joint load `f ∈ ℝ^{J × {0, 1}}` has a pair
of member forces and reactions in
[joint balance](../../../elasticity-and-structures/truss-equilibrium-load-envelopes-and-load-infere/joint-balance.md)
with it if and only if the
[equilibrium matrix](../../../elasticity-and-structures/truss-equilibrium-load-envelopes-and-load-infere/equilibrium-matrix.md)
`A` and the augmented matrix `(A | f)` have the same rank, by the
[Rouché–Capelli theorem](../../../../LinearAlgebra/matrix-decompositions/rouche-capelli-theorem/rouche-capelli.md).
