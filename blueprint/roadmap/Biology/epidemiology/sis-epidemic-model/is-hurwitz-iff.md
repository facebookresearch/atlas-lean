# Linearized threshold, stable side

For `β ≥ 0`, `γ > 0`, the eigenvalue `β - γ` of
`F - V` has negative real part iff `β < γ`, i.e. iff `R₀ < 1`
(`NextGenerationMatrix.isHurwitz_sub_iff_R0_lt_one` with `R0_eq`). This is the local spectral
statement only; global extinction is `IsSolution.tendsto_infected_zero`.
