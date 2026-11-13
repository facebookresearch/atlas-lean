# Aipw Score

The **AIPW score** for the average treatment effect with candidate propensity `e` and
candidate outcome regressions `m₀, m₁`, all fixed functions of the covariate value:
`m₁(X) - m₀(X) + 1_T (Y - m₁(X)) / e(X) - 1_{Tᶜ} (Y - m₀(X)) / (1 - e(X))`. Since Lean sets
`x / 0 = 0`, a unit with `e(X) = 0` (resp. `e(X) = 1`) has its treated (resp. control) residual
dropped; positivity of the candidate rules this out. This is an argument-order compatibility
alias for `MissingOutcomes.aipwATEScore`, so its integral theorems apply directly.
