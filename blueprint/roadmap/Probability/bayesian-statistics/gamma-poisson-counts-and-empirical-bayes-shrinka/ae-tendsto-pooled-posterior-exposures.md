# Almost-sure posterior consistency with different exposures

Let `μ` be a probability measure, `a > 0`, `b > 0`, `r₀ ≥ 0` and `B, C` real numbers. Let the cells
`i = 0, 1, …` have size factors (exposures) `sᵢ ∈ [0, B]` with total exposure `Sₙ = ∑_{i<n} sᵢ → ∞`,
and let the cell counts `X₀, X₁, …` (natural numbers) be pairwise independent and square-integrable,
with `E Xᵢ = sᵢ r₀` and `Var Xᵢ ≤ C sᵢ`; for `Xᵢ ~ Po(sᵢ r₀)` one can take `C = r₀`, see
[Poisson counts](ae-tendsto-pooled-posterior-poisson.md). Write `Kₙ = ∑_{i<n} Xᵢ`. Then almost
surely the pooled posterior `Gamma(a + Kₙ, b + Sₙ)` over the first `n` cells has mean
`(a + Kₙ) / (b + Sₙ) → r₀` and variance `(a + Kₙ) / (b + Sₙ)² → 0`, and the mass that
`Gamma(a + Kₙ, b + Sₙ)` assigns to `{x : |x − r₀| ≥ ε}`, outside the neighbourhood
`(r₀ − ε, r₀ + ε)`, tends to `0` for every `ε > 0`.

## Sources

- A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, D. B. Rubin, *Bayesian Data
  Analysis*, 3rd ed., CRC Press (2013), §2.6.
- A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, D. B. Rubin, *Bayesian Data
  Analysis*, 3rd ed., CRC Press (2013), Appendix B.
