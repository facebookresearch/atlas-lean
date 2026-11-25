# The transposed compatibility matrix collects member end forces

Let `J` (joints) and `M` (members) be finite sets, with joint positions `r_j` in the plane and
member `e` joining joint `a_e` to joint `b_e`. For member coefficients `c_e`, let the member exert
the force `c_e (r_{b_e} - r_{a_e})` on its start joint `a_e` and the opposite force on its end joint
`b_e`. Then, at every joint `j` and coordinate `k ∈ {0, 1}`, the
[compatibility matrix](axial-compatibility.md) `B` satisfies
`(Bᵀ c)(j, k) = -∑ (forces on joint j)_k`, the sum running over the member endpoints at joint `j`.
