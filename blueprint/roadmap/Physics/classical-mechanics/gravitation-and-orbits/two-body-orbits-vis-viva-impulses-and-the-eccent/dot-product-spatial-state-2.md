# The embedded circular orbit stays at distance R from the center

For planar position and velocity functions `r, v : ℝ → ℂ` satisfying the
[circular-orbit premises](is-circular-orbit.md) with gravitational parameter `μ` and radius `R`
(`μ > 0`, `R > 0`, and for every real time `t`: `|r(t)| = R`, `r'(t) = v(t)` and
`v'(t) = −(μ / |r(t)|³) r(t)`), every rotation matrix `Q ∈ SO(3)` and every time `t`, the
[spatial position](spatial-state.md) `X = Q (Re r(t), Im r(t), 0)` satisfies `X · X = R²`, so its
Euclidean distance from the center is `R`.
