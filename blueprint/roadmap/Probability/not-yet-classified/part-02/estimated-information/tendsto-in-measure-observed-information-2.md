# Consistency of the observed information at a consistent estimator

In addition to the
hypotheses of `tendstoInMeasure_observedInformation`, assume the Lipschitz envelope
`‖D_θ score p θ x - D_θ score p θ₀ x‖ ≤ M x ‖θ - θ₀‖` on the ball of radius `δ > 0` about
`θ₀` with integrable `M` (as in `VectorInference`). Then for any a.e.-measurable estimators
`θhat n → θ₀` in probability, `Ĵₙ(θhat n) → I(θ₀)` in probability. No measurability of
`(θ, x) ↦ D_θ score p θ x` is needed.

## Sources

- van der Vaart (1998), §5.6 (consistency of the plug-in observed information).
