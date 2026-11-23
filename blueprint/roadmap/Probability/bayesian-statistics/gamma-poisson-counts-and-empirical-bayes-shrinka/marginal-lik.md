# Marginal likelihood of a count under the Gamma–Poisson hierarchy

For real numbers `a, b, s` and a count `k ∈ ℕ`, the marginal likelihood is
`m(k) = ∫ P(k ∣ r) Gamma(a, b)(dr)`, the integral of the
[Poisson likelihood](poisson-exposure-lik.md) against the Gamma law with shape `a` and rate `b`,
taken to be `0` when the integrand is not integrable. For `a > 0`, `b > 0` and `s ≥ 0` it is the
prior-predictive probability of `k` under the hierarchy `k ∣ λ ~ Po(s λ)`, `λ ~ Gamma(a, b)`; for
other `a` or `b`, `Gamma(a, b)` is not a probability law.
