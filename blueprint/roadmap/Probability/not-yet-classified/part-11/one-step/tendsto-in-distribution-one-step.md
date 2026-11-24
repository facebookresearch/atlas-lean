# One-step estimator asymptotic normality

From a `√n`-bounded starter, one Newton
step with the score sum (`θ_init + J⁻¹ S_n(θ_init)/n`) is asymptotically normal with the
`+J⁻¹ Y` limit law. The score CLT is `VectorInference.tendstoInDistribution_score`, and the
strong law for the envelope average `n⁻¹ ∑ |M (X i)|` is `VectorInference.ae_tendsto_average`.
`hdiff` is needed because `hlip` constrains only `fderiv`, which is `0` wherever the score is
not differentiable, so `hlip` alone allows a score with a jump; `hscore_meas` makes the score
sums at the random starter measurable.
