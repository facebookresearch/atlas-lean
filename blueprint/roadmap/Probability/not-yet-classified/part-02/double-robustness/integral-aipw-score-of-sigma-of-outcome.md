# Double robustness, outcome regressions correct

If `g₀ = E[Y₀ | m]` and
`g₁ = E[Y₁ | m]` a.e., the AIPW score is unbiased for the average treatment effect for *any*
candidate propensity `e` with `ε ≤ e ≤ 1 - ε` (population level, fixed nuisances). The true
propensity `e*` may reach `0` or `1` here, but then the correct regression `g₁ = μ₁*` (on
`{e* = 0}`) or `g₀ = μ₀*` (on `{e* = 1}`) is not identified from the law of the observed data.
