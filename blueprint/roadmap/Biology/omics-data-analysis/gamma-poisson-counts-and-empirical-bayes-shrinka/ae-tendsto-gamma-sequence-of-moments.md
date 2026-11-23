# Almost-sure convergence of the Gamma sequence `Gamma(a + Kₙ, b + Sₙ)`

A purely analytic
statement: let `s₀, s₁, …` be reals with `sᵢ ≤ B` and `Sₙ = ∑_{i<n} sᵢ → ∞`, and let the counts
`X₀, X₁, …` (natural numbers) be pairwise independent and square-integrable with mean
`E Xᵢ = sᵢ r₀` for some `r₀ ≥ 0` and variance `Var Xᵢ ≤ C sᵢ`. Then almost surely, for `a, b > 0`
and `Kₙ = ∑_{i<n} Xᵢ`, the ratio `(a + Kₙ) / (b + Sₙ)` (`posteriorMean`) tends to `r₀`,
`(a + Kₙ) / (b + Sₙ)²` tends to `0`, and the mass that `gammaMeasure (a + Kₙ) (b + Sₙ)` assigns
outside every neighbourhood `(r₀ - ε, r₀ + ε)` tends to `0`.

No sign condition on `sᵢ` is imposed (for `r₀ > 0`, `sᵢ ≥ 0` follows from `E Xᵢ = sᵢ r₀ ≥ 0`), so
`b + Sₙ` may be nonpositive for small `n` and these Gamma laws need not be posteriors. For
nonnegative exposures they are the pooled posteriors: see `ae_tendsto_pooledPosterior_exposures`.
The counts are not identically distributed, so Mathlib's `ProbabilityTheory.strong_law_ae` does
not apply; `Kₙ / Sₙ → r₀` comes from `ProbabilityTheory.ae_tendsto_sum_div_sum_integral`.
