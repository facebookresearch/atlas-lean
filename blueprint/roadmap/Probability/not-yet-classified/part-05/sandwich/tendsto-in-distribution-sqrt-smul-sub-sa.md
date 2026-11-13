# Asymptotic normality of a GEE estimator with sandwich covariance

Let `U k β ω` be independent cluster scores. At the true parameter `β₀` assume the cluster
scores are measurable, independent, unbiased (`E[U k β₀] = 0`), and square integrable, that the
averaged projected variances converge to the meat quadratic form `⟪B t, t⟫` (the hypotheses
identify `B` only through this quadratic form; `B` need not be self-adjoint, and
`B` is not assumed positive definite), and that every projection satisfies the cluster
Lindeberg condition. Let the sensitivity matrix `A` be invertible, and let `βhat n` be a root
of the estimating equation with probability tending to one that linearizes with derivative
`A` (as in `tendstoInDistribution_sqrt_smul_sub_of_linearization`). Then
`√n • (βhat n - β₀)` converges in distribution to every `W` whose projections `⟪W, t⟫` are
centered Gaussians with variance `⟪A⁻¹ B A⁻ᵀ t, t⟫`, i.e. `W ∼ N(0, sandwichCovariance A B)`,
where the sandwich is the self-adjoint symmetrized covariance above.

The CLT is applied to the cluster sums of the transformed scores `-A⁻¹ U k β₀`.
