# Asymptotic normality of the method-of-moments estimator

Let `X₀, X₁, …` be i.i.d. counts
with law `μX` on `ℕ`, with finite fourth moment and with the negative binomial mean
`m = σ a / b` and second moment `m + m² / a + m²` at the true hyperparameter `(a, b)`,
`a, b, σ > 0`. Then the moment estimates `θhat n = momEstimator σ X n` satisfy
`√n (θhat n - (a, b)) → -J⁻¹ Y` in distribution, with `J = momJacobian a b σ` and
`Y ~ N(0, E[g gᵀ])`, `g = momEstFun σ (a, b) K`, given through its projections. Unlike
`tendstoInDistribution_countMLE`, no root or consistency hypothesis is needed: the moment estimate
solves the moment equations once the sample is overdispersed (`sum_momEstFun_mom_eq_zero`), which
happens with probability tending to one, and it is strongly consistent by the strong law.

## Sources

- the delta method for moment estimators (van der Vaart 1998, §4.1 and Theorem 5.41); instantiated from `VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation`.
