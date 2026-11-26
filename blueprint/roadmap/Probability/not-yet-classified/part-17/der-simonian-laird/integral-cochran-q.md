# Expectation of Cochran's `Q`

Let `μ` be a
probability measure, `k ≥ 2`, `v_i > 0` known sampling variances, `Δ² ≥ 0`, and
`y_i = m + δ_i + e_i` where `δ, e` satisfy the random-effects model assumptions (square
integrable, mean `0`, `Var δ_i = Δ²`, `Var e_i = v_i`, distinct deviations uncorrelated). Then
`S₁ - S₂ / S₁ > 0` and `E[cochranQ v y] = (k - 1) + Δ² (S₁ - S₂ / S₁)`, with `S_r = ∑ (v_i⁻¹)^r`.

## Sources

- R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Control. Clin. Trials 7 (1986) 177–188, p. 182 (the moment equation).
