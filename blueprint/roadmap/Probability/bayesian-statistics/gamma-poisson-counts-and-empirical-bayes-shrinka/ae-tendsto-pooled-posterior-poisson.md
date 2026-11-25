# Posterior consistency for Poisson counts with different exposures

Let `μ` be a probability measure, `a > 0`, `b > 0`, `r₀ ≥ 0` and `B` a real number. Let the size
factors `sᵢ ∈ [0, B]`, `i = 0, 1, …`, have total exposure `Sₙ = ∑_{i<n} sᵢ → ∞`, and let the cell
counts `Xᵢ` be pairwise independent with `Xᵢ ~ Po(sᵢ r₀)`. Write `Kₙ = ∑_{i<n} Xᵢ`. Then almost
surely the pooled posterior `Gamma(a + Kₙ, b + Sₙ)` has mean `(a + Kₙ) / (b + Sₙ) → r₀` and variance
`(a + Kₙ) / (b + Sₙ)² → 0`, and the mass that `Gamma(a + Kₙ, b + Sₙ)` assigns to
`{x : |x − r₀| ≥ ε}`, outside the neighbourhood `(r₀ − ε, r₀ + ε)`, tends to `0` for every `ε > 0`.
