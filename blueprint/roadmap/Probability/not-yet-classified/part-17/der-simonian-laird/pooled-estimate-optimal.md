# The random-effects pooled estimate with known `Δ²`

Under the hypotheses of `integral_cochranQ` (probability measure `μ`, `k ≥ 2`, sampling variances
`v_i > 0`, `Δ² ≥ 0`, `y_i = m + δ_i + e_i` with the random-effects model assumptions), the pooled
estimate `∑ᵢ ωᵢ yᵢ` with the inverse-variance weights `ω` of `v_i + Δ²` has expectation `m` and
variance `(∑ᵢ (v_i + Δ²)⁻¹)⁻¹`, and every weighted average `∑ c_i y_i` with `∑ c_i = 1` has
variance at least `(∑ᵢ (v_i + Δ²)⁻¹)⁻¹`.

## Sources

- R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7 (1986) 177–188, p. 183, equations (2)–(4).
