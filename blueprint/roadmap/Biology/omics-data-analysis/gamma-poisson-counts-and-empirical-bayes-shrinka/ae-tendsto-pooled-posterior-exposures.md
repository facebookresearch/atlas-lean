# Almost-sure posterior consistency of the pooled posterior with different exposures

Let cells `i = 0, 1, …` have nonnegative size factors (exposures) `sᵢ ∈ [0, B]` with divergent
total exposure `Sₙ = ∑_{i<n} sᵢ → ∞`, and let the cell counts `X₀, X₁, …` (natural numbers) be
pairwise independent and square-integrable with mean `E Xᵢ = sᵢ r₀` at a true rate `r₀ ≥ 0` and
variance `Var Xᵢ ≤ C sᵢ` (for `Xᵢ ~ Po(sᵢ r₀)`, `C = r₀`; see
`ae_tendsto_pooledPosterior_poisson`). Then almost surely, for the prior `Gamma(a, b)`
(`a, b > 0`), the pooled posterior `Gamma(a + Kₙ, b + Sₙ)` over the first `n` cells
(`Kₙ = ∑_{i<n} Xᵢ`) has mean tending to `r₀`, variance tending to `0`, and mass outside every
neighbourhood `(r₀ - ε, r₀ + ε)` tending to `0`. This is `ae_tendsto_gammaSequence_of_moments`
for nonnegative exposures.
