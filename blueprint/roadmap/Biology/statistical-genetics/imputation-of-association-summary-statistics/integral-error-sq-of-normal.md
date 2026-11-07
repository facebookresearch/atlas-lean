# Mean squared error of imputation with ImpG weights

For the ImpG weights (`Σ_oo w = Σ_ot`) the mean squared imputation error is
`Σ_tt - wᵀ Σ_ot = Σ_tt - Σ_to Σ_oo⁻¹ Σ_ot`, the linear-prediction residual variance
(the conditional variance only under the Gaussian ImpG model).
