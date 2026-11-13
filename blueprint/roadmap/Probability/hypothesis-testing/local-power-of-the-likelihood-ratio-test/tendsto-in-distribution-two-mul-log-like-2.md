# Local power of the likelihood-ratio test

Let row `n` of the triangular array
`X n 0, X n 1, …` be i.i.d. with law `p θₙ ν`, `θₙ = θ₀ + h / √n`, under the Cramér conditions
at `θ₀` of `LikelihoodRatioTests.tendstoInDistribution_two_mul_logLikelihood_sub` (all moment
and envelope conditions are under the null law `p θ₀ ν`). If `θ̂ₙ` solves the likelihood
equation for row `n` with probability tending to one and `θ̂ₙ → θ₀` in probability, then
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀))` converges in distribution to the law of `(Z + h √I(θ₀))²`,
`Z ~ N(0, 1)` (noncentral `χ²₁` with noncentrality `h² I(θ₀)`). For `h = 0` this is Wilks'
theorem for a triangular array.

The row `n = 0` is irrelevant for the limit; with Lean's `h / √0 = 0` its law is `p θ₀ ν`, which
makes `p θ₀ ν` a probability measure. No normalization `∫ p θ dν = 1` is assumed otherwise:
the laws `p θₙ ν` are probability measures because they are laws of random variables.

## Sources

- van der Vaart (1998), ch. 16 (local power), via local asymptotic normality (ch. 7) and Le Cam's first and third lemmas (ch. 6).
