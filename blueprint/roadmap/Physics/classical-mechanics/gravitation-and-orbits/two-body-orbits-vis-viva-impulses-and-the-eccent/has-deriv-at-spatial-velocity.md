# The embedded circular orbit obeys the inverse-square law

For planar position and velocity functions `r, v : ℝ → ℂ` satisfying the
[circular-orbit premises](is-circular-orbit.md) with gravitational parameter `μ` and radius `R`
(`μ > 0`, `R > 0`, and for every real time `t`: `|r(t)| = R`, `r'(t) = v(t)` and
`v'(t) = −(μ / |r(t)|³) r(t)`), every rotation matrix `Q ∈ SO(3)` and every time `t`, the spatial
velocity `τ ↦ Q (Re v(τ), Im v(τ), 0)` has derivative `−(μ / |X|³) X` at `t`, where
`X = Q (Re r(t), Im r(t), 0)` is the [spatial position](spatial-state.md) and `|X| = √(X · X)`: the
inverse-square attraction toward the center, in inertial components.
