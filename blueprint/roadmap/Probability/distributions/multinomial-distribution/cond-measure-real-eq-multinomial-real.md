# Poisson conditioning

Let `Xᵢ ~ Po(λᵢ)`, `i ∈ ι`, be independent Poisson counts with
`∑ᵢ λᵢ > 0`. Given their total `∑ᵢ Xᵢ = N`, the count vector is multinomial with
`N` throws and cell probabilities `λᵢ / ∑ⱼ λⱼ`:
`P(X = x | ∑ᵢ Xᵢ = N) = multinomialReal N (λ / ∑ λ) x`.
