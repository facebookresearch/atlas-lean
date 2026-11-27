# Quantitative separation for the MLE

Let `Θ` be a compact metric space, `σ` a finite set and `law : Θ → (σ → ℝ)` continuous, positive and
normalized: `law θ a > 0` for all `θ` and `a`, and `∑_a law θ a = 1` for every `θ`. Let `θ₀` be
identified up to a set `E ⊆ Θ`: every `θ` with `law θ = law θ₀` lies in `E`. For every `ε > 0` there
is `η > 0` such that, for all frequencies `f : σ → ℝ` at sup distance less than `η` from `law θ₀`,
every maximizer `θ̂` of the [log-likelihood criterion](log-lik.md) `θ ↦ L(f, θ)` satisfies
`d(θ̂, E) < ε`, where `d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`.
