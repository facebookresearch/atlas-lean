# Asymptotic normality of consistent roots of the likelihood equation, vector parameter

(Cramér's conditions; limit written as `I(θ₀)⁻¹ Y` with `Y ~ N(0, I(θ₀))`). For i.i.d.
observations with law `p θ₀ ν`, assume on the ball of radius `δ > 0` about the interior point
`θ₀` that the score `θ ↦ score p θ x` is differentiable with Lipschitz derivative
`‖Dscore θ x - Dscore θ₀ x‖ ≤ M x ‖θ - θ₀‖` (integrable `M`); that the score at `θ₀` is
measurable, square integrable and centered; that `Dscore θ₀` is strongly measurable, integrable
and satisfies the **information identity** `E Dscore θ₀ = -I(θ₀)`; and that the Fisher
information `I(θ₀)` is **nonsingular**. For estimators `θhat n` that are roots of the likelihood
equation `∑_{i<n} score p θ (X i) = 0` with probability tending to one and are consistent (both
are hypotheses: existence and consistency of the roots are not derived here; consistency of a
maximum-likelihood estimator follows, under compactness and identifiability, from Wald's theorem
`FisherInformation.ae_tendsto_maximumLikelihood`), `√n (θhat n - θ₀) → I(θ₀)⁻¹ Y`.

The centering and information identities are what differentiating `∫ p θ dν = 1` twice under
the integral sign gives; they are assumed directly.

## Sources

- Cramér (1946), §33.3; Lehmann & Casella (1998), Theorem 6.5.1; van der Vaart (1998), Theorem 5.41.
