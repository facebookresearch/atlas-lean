# Quadratic expansion of the log-likelihood ratio

Let `θ̂ₙ` be `√n`-consistent
(`√n (θ̂ₙ - θ₀)` converges in distribution) and solve the likelihood equation with probability
tending to one. If on the ball of radius `δ > 0` about `θ₀` the log-likelihood is twice
differentiable in `θ` with `|∂³_θ log p θ x| ≤ M x` for an integrable `M`, and
`∂²_θ log p θ₀` is integrable with mean `-I(θ₀)`, then
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - n (θ̂ₙ - θ₀)² I(θ₀) → 0` in probability, where
`ℓₙ θ = ∑_{i<n} log p θ (X i)`.

The positivity of `p` is not used: the expansion holds for any criterion `log p θ x` with these
derivatives, and the theorems below assume `0 < p θ x`.

## Sources

- the second-order expansion of Wilks (1938); van der Vaart (1998), ch. 16.
