# Axial-force endpoint forces as coefficient endpoint forces

For joints with positions `r : J → ℝ²`, members `e ∈ M` joining `a(e)` and `b(e)` with
[lengths](member-length.md) `ℓ(e)`, and axial forces `N : M → ℝ`, the
[axial-force endpoint family](axial-endpoint-force.md) equals the
[coefficient endpoint family](member-endpoint-force.md) with coefficients
`c(e) = N(e) / ℓ(e)`. This holds for every table; with the convention `u / 0 = 0` a member with
coincident endpoints has `c(e) = 0` and both families give it zero forces.
