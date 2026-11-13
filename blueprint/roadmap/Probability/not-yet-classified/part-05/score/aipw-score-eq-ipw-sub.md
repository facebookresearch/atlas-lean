# The AIPW score as an augmented IPW contrast

When `e(X) ∉ {0, 1}`, the score is the IPW
contrast `1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X))` minus the propensity residual `1_T - e(X)`
times `m₁(X) / e(X) + m₀(X) / (1 - e(X))`. When `e` is the true propensity this residual term
has conditional mean zero given `X` (`condExp_propensityResidual_mul`).
