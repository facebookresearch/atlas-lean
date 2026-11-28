# Population shape score

For a measure `μ` on `Ω`, functions `S : Ω → ℝ` and `K : Ω → ℕ`, and reals `a`, `b`, the population
shape score is `G(a, b) = ∫ (∑_{j<K} 1 / (a + j) - log (1 + S / b)) dμ`. The integral is the Bochner
integral, `0` when the integrand is not integrable; outside the intended domain `a > 0`, `b > 0`,
`S > 0` the conventions `1 / 0 = 0`, `x / 0 = 0`, `log 0 = 0` and `log x = log |x|` apply. For a
probability measure it is the expected shape score `E[∑_{j<K} 1 / (a + j) - log (1 + S / b)]` of one
cell when the integrand is integrable, for example when `a > 0`, `b > 0`, `S > 0` and `S`, `K` are
measurable and integrable.

For `a > 0` and `b > 0`, if `(S₀, K₀), (S₁, K₁), …` are measurable, pairwise independent copies of
`(S, K)` on a probability space, with `S > 0` and `S`, `K` integrable, then `n⁻¹` times the
[shape score](../likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) of the first `n`
cells tends to `G(a, b)` almost surely by the strong law of large numbers.
