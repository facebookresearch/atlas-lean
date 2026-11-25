# Method-of-joints balance of a planar truss

Let `J` (joints), `M` (members) and `R` (reaction components) be finite sets, with joint positions
`r_j` in the plane, member `e` joining joint `a_e` to joint `b_e`, and reaction component `s` acting
at joint `sj_s` along the direction `sd_s` (a vector of the plane, not necessarily of unit length).
Member axial forces `N_e` (tension positive), reaction coefficients `ρ_s` (signed, the reaction
being `ρ_s sd_s`) and an external load `f(j, k)` at each joint coordinate are in joint balance when,
at every joint `j` and coordinate `k ∈ {0, 1}`, the forces the members exert on joint `j`,
`∑_{e : a_e = j} N_e * (u_e)_k - ∑_{e : b_e = j} N_e * (u_e)_k`, the reactions at `j`,
`∑_{s : sj_s = j} ρ_s * (sd_s)_k`, and the external load `f(j, k)` sum to zero. Here
`u_e = (r_{b_e} - r_{a_e}) / L_e` is the unit direction of member `e` from `a_e` to `b_e`, `L_e`
being its Euclidean length. A zero-length member exerts no force, its unit direction being `0` by
the convention `0⁻¹ = 0`.
