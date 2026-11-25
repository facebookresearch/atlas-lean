# Consistency in measure to the fibre of the true law

Let `Θ` be a compact metric space, `σ` a finite set, `law : Θ → (σ → ℝ)` continuous and `θ₀ ∈ Θ`,
and let `P` be any measure on `Ω`. If frequency estimates `freq n` converge to `law θ₀` in
`P`-measure, for the sup distance on `σ → ℝ`, then every
[minimum-distance estimator](is-min-dist-estimator.md) `est` for `law` and `freq` converges in
`P`-measure to the fibre `F = {θ : law θ = law θ₀}`: for every `ε > 0`,
`P {ω : d(est n ω, F) ≥ ε} → 0` as `n → ∞`, where `d(θ, F) = inf_{θ' ∈ F} d(θ, θ')`. No
identifiability is assumed. The estimator need not be measurable: `P` of a set that is not
measurable is its outer measure. For a probability measure `P` this is convergence in probability.
