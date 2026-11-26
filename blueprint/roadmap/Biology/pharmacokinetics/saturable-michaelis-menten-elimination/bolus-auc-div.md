# Bolus AUC per unit initial concentration

For every initial concentration `C₀ ≠ 0` and all real `Vmax` and `Km`, the [bolus AUC](bolus-auc.md)
`AUC(C₀) = C₀ * (Km + C₀ / 2) / Vmax` satisfies `AUC(C₀) / C₀ = (Km + C₀ / 2) / Vmax`; with the
convention `x / 0 = 0` both sides are `0` when `Vmax = 0`. Since `C₀ = D / V` for a dose `D` in a
volume `V`, this ratio is `V * AUC / D`, not the dose-normalized `AUC / D`.
