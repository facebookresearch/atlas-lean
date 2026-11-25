# On the embedded Kepler arc the position has derivative the velocity

For real functions `x, y, vx, vy` satisfying the
[planar Kepler-arc premises](is-planar-kepler-arc.md) with `μ`, `t₀`, `t₁` (`μ > 0`, `t₀ < t₁`, and
at every `t` in `[t₀, t₁]`: `ρ = √(x² + y²) > 0`, `x' = vx`, `y' = vy`, `vx' = −μ x / ρ³`,
`vy' = −μ y / ρ³`), every rotation matrix `Q ∈ SO(3)` and every `t` in `[t₀, t₁]`, the
[spatial position](spatial-state.md) `τ ↦ Q (x(τ), y(τ), 0)` has derivative the spatial velocity
`Q (vx(t), vy(t), 0)` at `t`.
