# Deterministic consistency of likelihood maximizers

Let `Θ` be a compact metric space, `σ` a finite set and `law : Θ → (σ → ℝ)` continuous, positive and
normalized: `law θ a > 0` for all `θ` and `a`, and `∑_a law θ a = 1` for every `θ`. Let `θ₀` be
identified up to a set `E ⊆ Θ`: every `θ` with `law θ = law θ₀` lies in `E`. If frequencies
`fₙ : σ → ℝ` converge to `law θ₀` and each `θ̂ₙ` maximizes the
[log-likelihood criterion](log-lik.md) `θ ↦ L(fₙ, θ)` over `Θ`, then `d(θ̂ₙ, E) → 0` as `n → ∞`,
where `d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`.
