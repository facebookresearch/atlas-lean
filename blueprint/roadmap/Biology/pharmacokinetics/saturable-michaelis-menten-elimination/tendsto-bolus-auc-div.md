# Low-dose limit

For all real `Vmax` and `Km`, the ratio `AUC(C₀) / C₀` of the [bolus AUC](bolus-auc.md)
`AUC(C₀) = C₀ * (Km + C₀ / 2) / Vmax` to the initial concentration tends to `Km / Vmax` as `C₀ → 0`
with `C₀ > 0`; with the convention `x / 0 = 0` the ratio and the limit are `0` when `Vmax = 0`. For
`Vmax, Km > 0` the limit is the value `1 / k` of the linear model with `k = Vmax / Km`. Since
`C₀ = D / V` for a dose `D` in a volume `V`, this ratio is `V * AUC / D`, not the dose-normalized
`AUC / D`.
