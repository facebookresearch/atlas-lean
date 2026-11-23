# MLE consistency in measure from convergent frequencies

Let `Θ` be a compact metric space, `σ` a finite set and `law : Θ → (σ → ℝ)` continuous, positive and
normalized: `law θ a > 0` for all `θ` and `a`, and `∑_a law θ a = 1` for every `θ`. Let `θ₀` be
identified up to a set `E ⊆ Θ`: every `θ` with `law θ = law θ₀` lies in `E`. Let `P` be any measure
on `Ω`. If frequency estimates `freq n` converge to `law θ₀` in `P`-measure, for the sup distance on
`σ → ℝ`, then every [maximum-likelihood estimator](is-mle.md) `est` for `law` and `freq` satisfies,
for every `ε > 0`, `P {ω : d(est n ω, E) ≥ ε} → 0` as `n → ∞`, where
`d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`. The estimator need not be measurable: `P` of a set that is not
measurable is its outer measure. For a probability measure `P` this is consistency in probability.
