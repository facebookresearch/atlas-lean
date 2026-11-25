# Lotka–Volterra time along a replicator solution

For a finite set `ι`, a curve `x : ℝ → (ι ∪ {o} → ℝ)` and a real `t`, the Lotka–Volterra time is
`τ(t) = ∫₀ᵗ x_o(max(s, 0)) ds`: for `t ≥ 0` it is `∫₀ᵗ x_o(s) ds`, and for `t < 0` it is
`t x_o(0)`. The speed is clamped at time `0` so that, for a
[replicator solution](../replicator-dynamics/is-solution.md) `x`, `τ` is a
[`C¹` function on `ℝ`](cont-diff-time-change.md); with the convention that the integral of a
non-integrable function is `0`, it is defined for every curve.
