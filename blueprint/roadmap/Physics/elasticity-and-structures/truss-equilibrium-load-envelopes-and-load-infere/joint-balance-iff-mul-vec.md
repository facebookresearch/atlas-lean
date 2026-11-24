# Joint balance is the equilibrium matrix equation

Let `J` (joints), `M` (members) and `R` (reaction components) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, and reaction component `s` acting
at joint `sj_s` along the direction `sd_s` (a vector of the plane, not necessarily of unit length).
For an external load `f`, member forces `N` and reaction coefficients `ρ`, the
[joint balance](joint-balance.md) holds if and only if `A (N, ρ) = f`, where `A` is the
[equilibrium matrix](equilibrium-matrix.md): `B_uᵀ N - R_sup ρ = f`. A zero-length member exerts no
force and gives a zero column, its unit direction being `0` by the convention `0⁻¹ = 0`.
