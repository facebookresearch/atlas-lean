# The transposed unit compatibility matrix collects axial end forces

Let `J` (joints) and `M` (members) be finite sets, with joint positions `r_j` in the plane and
member `e` joining joint `a_e` to joint `b_e`. For member axial forces `N_e` (tension positive), let
the member exert the force `N_e u_e` on its start joint `a_e` and `-N_e u_e` on its end joint `b_e`,
where `u_e = (r_{b_e} - r_{a_e}) / L_e` is its unit direction, `L_e` being the Euclidean length of
member `e`. Then, at every joint `j` and coordinate `k ∈ {0, 1}`, the
[unit-direction compatibility matrix](axial-compatibility-unit.md) `B_u` satisfies
`(B_uᵀ N)(j, k) = -∑ (forces on joint j)_k`, the sum running over the member endpoints at joint `j`.
A zero-length member exerts no force, by the convention `0⁻¹ = 0`.
