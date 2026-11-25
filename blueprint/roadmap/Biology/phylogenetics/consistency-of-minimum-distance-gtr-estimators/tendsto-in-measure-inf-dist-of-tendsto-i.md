# Consistency in measure up to the identified class

Let `Θ` be a compact metric space, `σ` a finite set, `law : Θ → (σ → ℝ)` continuous and `θ₀ ∈ Θ`
identified up to a set `E ⊆ Θ`: every `θ` with `law θ = law θ₀` lies in `E`. Let `P` be any measure
on `Ω`. If frequency estimates `freq n` converge to `law θ₀` in `P`-measure, for the sup distance on
`σ → ℝ`, then every [minimum-distance estimator](is-min-dist-estimator.md) `est` for `law` and
`freq` satisfies, for every `ε > 0`, `P {ω : d(est n ω, E) ≥ ε} → 0` as `n → ∞`, where
`d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`. The estimator need not be measurable: `P` of a set that is not
measurable is its outer measure. For a probability measure `P` this is consistency in probability.
