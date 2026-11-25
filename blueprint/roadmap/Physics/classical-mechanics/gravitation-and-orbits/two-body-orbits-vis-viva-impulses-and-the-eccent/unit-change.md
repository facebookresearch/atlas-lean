# Changes of units with positive factors preserve a circular orbit

Let `l > 0` and `s > 0` be the numbers of new length and time units per old unit (for example
`l = 1000` from kilometres to metres and `s = 1 / 3600` from seconds to hours), so that a time `t`
becomes `τ = s t`. If planar position and velocity functions `r, v : ℝ → ℂ` satisfy the
[circular-orbit premises](is-circular-orbit.md) with gravitational parameter `μ` and radius `R`,
then the rescaled position `τ ↦ l r(τ / s)` and velocity `τ ↦ (l / s) v(τ / s)` satisfy them with
gravitational parameter `(l³ / s²) μ` and radius `l R`: lengths scale by `l`, speeds by `l / s`, and
the gravitational parameter, of dimension `L³ T⁻²`, by `l³ / s²`.
