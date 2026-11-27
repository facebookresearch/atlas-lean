# Liability-scale LD-score regression estimator

For a real threshold `t`, a real case fraction `P`, natural numbers `N` (individuals) and `M`
(markers), and real vectors `ℓ = (ℓ_1, …, ℓ_M)` (LD scores) and `χ = (χ_1, …, χ_M)` (association
statistics), the liability-scale LD-score regression estimator is

`ĥ²_l = (K² (1 - K)² / (P (1 - P) z²)) · ĥ²`,

the [case-control conversion factor](cc-liability-factor.md) times the
[unweighted LD-score regression estimator](../ld-score-regression/ols-h2-hat.md) `ĥ² = b̂ M / N`,
where `b̂` is the least-squares slope of `χ` on `ℓ`; here `K = K(t)` is the
[prevalence](prevalence.md) and `z = z(t)` the
[standard normal density at the threshold](threshold-density.md). Both factors are defined for all
inputs: with the convention `x / 0 = 0` the conversion factor is `0` at `P = 0` and at `P = 1`, and
`ĥ²` is `0` when `N = 0` or when the LD scores are all equal.
