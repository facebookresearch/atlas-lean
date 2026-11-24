# Wald's argmax theorem

Let `Θ` be a compact metric space, `M : Θ → ℝ` continuous, `θ₀ ∈ Θ`, and `E ⊆ Θ` a set containing
every `θ` with `M θ ≥ M θ₀`. If functions `Mₙ : Θ → ℝ` converge to `M` uniformly on `Θ` and each
`θ̂ₙ` maximizes `Mₙ` over `Θ`, then `d(θ̂ₙ, E) → 0` as `n → ∞`, where
`d(θ, E) = inf_{θ' ∈ E} d(θ, θ')`. This is the deterministic core of Newey and McFadden's Theorem
2.1.
