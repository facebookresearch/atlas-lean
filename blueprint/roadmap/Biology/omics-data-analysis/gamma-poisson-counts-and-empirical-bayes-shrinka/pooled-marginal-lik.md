# Joint marginal likelihood of the cell counts

For real numbers `a` and `b`, a finite set of cells with real size factors `sⱼ` and counts `kⱼ ∈ ℕ`,
the joint marginal likelihood is `∫ L(k ∣ r) Gamma(a, b)(dr)`, the integral of the
[joint likelihood](pooled-lik.md) against the Gamma law with shape `a` and rate `b`, taken to be `0`
when the integrand is not integrable. For `a > 0`, `b > 0` and `sⱼ ≥ 0` it is the prior-predictive
probability of the counts under the shared prior `λ ~ Gamma(a, b)`.
