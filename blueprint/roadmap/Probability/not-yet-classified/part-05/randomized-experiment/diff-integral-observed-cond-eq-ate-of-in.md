# Identification of the ATE under random assignment

If the treatment indicator `1_T` is
independent of the pair of potential outcomes `(Y₀, Y₁)`, both arms have positive probability,
and the potential outcomes are integrable, then the difference of the observed group means
identifies the average treatment effect, `E[Y | T] - E[Y | Tᶜ] = E[Y₁ - Y₀]`, where
`Y = observed T Y₀ Y₁` (consistency).
