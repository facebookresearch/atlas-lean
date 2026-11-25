# For s ≠ 1, scaling μ by l³ without 1 / s² gives no circular orbit

Let `l > 0` and `s > 0` with `s ≠ 1`, and let planar position and velocity functions `r, v : ℝ → ℂ`
satisfy the [circular-orbit premises](is-circular-orbit.md) with gravitational parameter `μ` and
radius `R`. Then the rescaled position `τ ↦ l r(τ / s)` and velocity `τ ↦ (l / s) v(τ / s)` do not
satisfy the circular-orbit premises with radius `l R` and gravitational parameter `l³ μ`, which
leaves out the factor `1 / s²` of the [consistent change of units](unit-change.md): a wrong time
unit is rejected.
