# Consistency of the empirical sandwich estimator

**Consistency of the empirical sandwich estimator** `Ahat⁻¹ Bhat Ahat⁻ᵀ` with plug-in bread
`Ahat n = n⁻¹ • ∑_{i<n} DU i (βhat n)` and plug-in meat
`Bhat n = n⁻¹ • ∑_{i<n} U i (βhat n) U i (βhat n)ᵀ`. Assume the averaged Jacobians and the
averaged rank-one operators of the cluster scores converge uniformly on a ball around `β₀` in
probability to `Abar` and `Bbar`, both continuous at `β₀`, that `Abar β₀` is invertible, and
that `βhat` is consistent. Then the empirical sandwich converges in probability to
`sandwichCovariance (Abar β₀) (Bbar β₀)`.

This is the asymptotic covariance of `tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt`
(same `Abar` and Jacobian hypothesis) only when `Bbar β₀` equals the CLT meat `B`, which this
theorem does not assume; see `tendstoInMeasure_empirical_sandwichCovariance_of_eq`.
