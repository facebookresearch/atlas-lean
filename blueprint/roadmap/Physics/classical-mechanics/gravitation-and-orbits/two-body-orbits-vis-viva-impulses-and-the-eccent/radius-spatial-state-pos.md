# The embedded Kepler arc stays away from the center

For real functions `x, y, vx, vy` satisfying the
[planar Kepler-arc premises](is-planar-kepler-arc.md) with `μ`, `t₀`, `t₁` (`μ > 0`, `t₀ < t₁`, and
at every `t` in `[t₀, t₁]`: `ρ = √(x² + y²) > 0`, `x' = vx`, `y' = vy`, `vx' = −μ x / ρ³`,
`vy' = −μ y / ρ³`), every rotation matrix `Q ∈ SO(3)` and every `t` in `[t₀, t₁]`, the
[spatial position](spatial-state.md) `X = Q (x(t), y(t), 0)` has positive distance `√(X · X) > 0`
from the center.
