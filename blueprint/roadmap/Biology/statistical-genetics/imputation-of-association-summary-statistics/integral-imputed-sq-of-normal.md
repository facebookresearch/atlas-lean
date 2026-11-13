# Second moment of the statistic imputed with ImpG weights

For the ImpG weights (`Σ_oo w = Σ_ot`, i.e. `w = Σ_oo⁻¹ Σ_ot` when `Σ_oo` is invertible) the
imputed statistic has second moment `wᵀ Σ_ot = Σ_to Σ_oo⁻¹ Σ_ot`; for `Σ_tt = 1` this is
`1 -` the linear-prediction residual variance, ImpG's `r²_pred`.
