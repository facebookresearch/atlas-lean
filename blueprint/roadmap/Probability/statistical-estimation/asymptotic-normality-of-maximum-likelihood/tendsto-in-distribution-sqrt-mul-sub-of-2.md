# Asymptotic normality of consistent roots of the likelihood equation

**Asymptotic normality of consistent roots of the likelihood equation** (Cramér's
conditions). Let `p θ` be positive
densities with respect to `ν`, and on the ball of radius `δ > 0` about `θ₀` let each `p θ` be
measurable with `∫ p θ dν = 1`, so that the family is a statistical model there (as in
`FisherInformation.cramerRao`). The proof uses measurability only at `θ₀` and does not use the
normalization `_hp_int`: the limit theorem holds for roots of any criterion with these
derivatives.
Let `X 0, X 1, …` be i.i.d. with law `p θ₀ ν`. Assume that on the same ball the log-likelihood
`log p θ x` is differentiable in `θ` for every `x` (so that `score p θ x` is its true derivative
there, not Lean's junk value `0` of `deriv` at a nondifferentiable point) and the score
`∂_θ log p θ x` is twice differentiable in `θ` for every `x`, with `|∂³_θ log p θ x| ≤ M x`
for an integrable `M`; that the score `∂_θ log p θ₀` is measurable and square integrable with
mean zero; that `∂²_θ log p θ₀` is measurable and integrable with `E ∂²_θ log p θ₀ = -I(θ₀)`
(the information identity); and that `0 < I(θ₀)`. The two moment identities are what
differentiating `∫ p θ dν = 1` twice under the integral sign gives; they are assumed directly.
Let `θhat n` be estimators that solve the likelihood equation `∑_{i<n} ∂_θ log p θ (X i) = 0`
with probability tending to one and converge to `θ₀` in probability. Then
`√n (θhat n - θ₀) → N(0, 1 / I(θ₀))` in distribution. The roots need not maximize the
likelihood; for a maximum-likelihood estimator, consistency and the likelihood equation must
be established separately (for example, from an interior maximum of a differentiable
likelihood).

## Sources

- Cramér (1946), §33.3; Lehmann & Casella (1998), Theorem 6.3.10; van der Vaart (1998), Theorem 5.41.
