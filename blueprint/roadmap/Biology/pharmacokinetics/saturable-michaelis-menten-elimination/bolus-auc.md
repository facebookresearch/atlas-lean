# Closed-form bolus AUC

For real numbers `Vmax`, `Km` and `C₀`, the bolus AUC is `AUC(C₀) = C₀ * (Km + C₀ / 2) / Vmax`. It
is defined for all real inputs; with the convention `x / 0 = 0` it is `0` when `Vmax = 0`. For
`Vmax > 0`, `Km > 0` and `C₀ ≥ 0` it is the
[area under the concentration curve](integral-ioi-bolus.md) after a bolus giving the initial
concentration `C₀`.
