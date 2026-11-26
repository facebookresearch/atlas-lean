# Population rate score in the log rate

For a measure `μ` on `Ω`, functions `S : Ω → ℝ` and `K : Ω → ℕ`, and reals `a`, `b`, the population
rate score in the log rate is `R(a, b) = a - ∫ (a + K) · b / (b + S) dμ`. The integral is the
Bochner integral, `0` when the integrand is not integrable, and `b / (b + S) = 0` where `b + S = 0`
(`x / 0 = 0`). For a probability measure, a measurable `S > 0` and a measurable, integrable `K` it
is `a - E[(a + K) b / (b + S)]`, the population counterpart of the
[rate score times the rate](../likelihood-equations-and-efficiency-of-the-gamma/rate-score-log.md)
of one cell with size factor `S` and count `K`.

For `a ≥ 0` and `b > 0`, if `(S₀, K₀), (S₁, K₁), …` are measurable, pairwise independent copies of
`(S, K)` on a probability space, with `S > 0` and `K` integrable, then `n⁻¹` times the rate score
times the rate of the first `n` cells, `n⁻¹ ∑_{i<n} (a - (a + Kᵢ) b / (b + Sᵢ))`, tends to `R(a, b)`
almost surely by the strong law of large numbers. If `R(a, b₀) = 0` with `a > 0` and `b₀ > 0`, the
[rate root](rate-root.md) of the first `n` cells tends to `b₀` almost surely
([strong consistency of the rate root](ae-tendsto-rate-root.md)).
