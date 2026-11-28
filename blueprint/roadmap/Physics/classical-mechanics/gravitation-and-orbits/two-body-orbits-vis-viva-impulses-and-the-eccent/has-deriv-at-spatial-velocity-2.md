# On the embedded Kepler arc the velocity obeys the inverse-square law

For real functions `x, y, vx, vy` satisfying the
[planar Kepler-arc premises](is-planar-kepler-arc.md) with `μ`, `t₀`, `t₁` (`μ > 0`, `t₀ < t₁`, and
at every `t` in `[t₀, t₁]`: `ρ = √(x² + y²) > 0`, `x' = vx`, `y' = vy`, `vx' = −μ x / ρ³`,
`vy' = −μ y / ρ³`), every rotation matrix `Q ∈ SO(3)` and every `t` in `[t₀, t₁]`, the spatial
velocity `τ ↦ Q (vx(τ), vy(τ), 0)` has derivative `−(μ / |X|³) X` at `t`, where
`X = Q (x(t), y(t), 0)` is the [spatial position](spatial-state.md) and `|X| = √(X · X)`: the
inverse-square attraction toward the center.
