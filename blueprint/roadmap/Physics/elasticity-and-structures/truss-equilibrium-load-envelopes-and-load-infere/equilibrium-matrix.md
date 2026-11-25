# Equilibrium matrix of a planar truss

Let `J` (joints), `M` (members) and `R` (reaction components) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, and reaction component `s` acting
at joint `sj_s` along the direction `sd_s` (a vector of the plane, not necessarily of unit length).
The equilibrium matrix is `A = [B_uᵀ | -R_sup]`: its rows are the joint coordinates `(j, k)`,
`k ∈ {0, 1}`; its columns are the member forces, then the reaction components. Here `B_u` is the
[unit-direction compatibility matrix](../pin-jointed-trusses/axial-compatibility-unit.md), whose row
`e` has the entry `(r_{b_e} - r_{a_e})_k / L_e` at the coordinate `(b_e, k)` and its negative at
`(a_e, k)` (the two cancel when `a_e = b_e`), `L_e` being the Euclidean length of member `e`, and
`R_sup` is the [reaction matrix](reaction-matrix.md). A zero-length member gives a zero column, its
unit direction being `0` by the convention `0⁻¹ = 0`.
