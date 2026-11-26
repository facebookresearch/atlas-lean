# Replicator time along a Lotka–Volterra solution

For a finite set `ι`, a curve `y : ℝ → (ι → ℝ)` and a real `τ`, the replicator time is
`t(τ) = ∫₀^τ (1 + ∑_j y_j(max(σ, 0))) dσ`: for `τ ≥ 0` it is `∫₀^τ (1 + ∑_j y_j(σ)) dσ`, and for
`τ < 0` it is `τ (1 + ∑_j y_j(0))`. The integrand is clamped at time `0`, as for the
[Lotka–Volterra time](time-change.md); with the convention that the integral of a non-integrable
function is `0`, it is defined for every curve.
