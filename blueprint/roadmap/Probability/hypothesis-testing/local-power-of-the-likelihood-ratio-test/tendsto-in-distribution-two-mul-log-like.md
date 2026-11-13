# Wilks' expansion for a triangular array

Let `X n i` be random variables (row `n` is the
sample of size `n`) and `θ̂ₙ` estimators that solve the likelihood equation
`∑_{i<n} ∂_θ log p θ (X n i) = 0` with probability tending to one and converge to `θ₀` in
probability. Suppose that on the ball of radius `δ > 0` about `θ₀` the log-likelihood is
differentiable in `θ`, the score is twice differentiable, and `|∂³_θ log p θ x| ≤ M x`. Assume
the laws of large numbers `-(n⁻¹ ∑_{i<n} ∂²_θ log p θ₀ (X n i)) → I` with `I > 0` and
`n⁻¹ ∑_{i<n} M (X n i) → c` in probability, and that the normalized score
`n^{-1/2} ∑_{i<n} ∂_θ log p θ₀ (X n i)` converges in distribution to `Y`. Then
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) → Y² / I` in distribution, where `ℓₙ θ = ∑_{i<n} log p θ (X n i)`.

No independence or distributional assumption on the rows is made: they enter only through the
three limit hypotheses. The positivity of `p` is not used either: the expansion holds for any
criterion `log p θ x` with these derivatives. For i.i.d. rows with law `p θ₀ ν` this is Wilks'
theorem; under local alternatives it gives the local power
(`tendstoInDistribution_two_mul_logLikelihood_sub_local`).

## Sources

- Wilks (1938); van der Vaart (1998), Theorem 5.41 and ch. 16.
