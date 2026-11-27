# Joint balance with a nonsingular square equilibrium matrix

Let `J` (joints), `M` (members) and `R` (reaction components) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, and reaction component `s` acting
at joint `sj_s` along the direction `sd_s` (a vector of the plane, not necessarily of unit length).
For a bijection `e` from the unknowns (members, then reaction components) to the joint coordinates,
let `A_sq` be the [square equilibrium matrix](square-equilibrium-matrix.md), with row `u` equal to
row `e(u)` of the [equilibrium matrix](equilibrium-matrix.md). If `det A_sq ≠ 0`, then for every
external load `f`, member forces `N` and reaction coefficients `ρ`, the
[joint balance](joint-balance.md) holds if and only if `(N, ρ) = A_sq⁻¹ (f ∘ e)`. A zero-length
member would give a zero column, so the hypothesis excludes it.
