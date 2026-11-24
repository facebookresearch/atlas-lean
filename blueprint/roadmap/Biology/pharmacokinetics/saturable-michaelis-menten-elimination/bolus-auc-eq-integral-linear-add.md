# AUC splits into a linear and a saturation part

For `Vmax > 0`, `Km > 0`, a volume `V > 0` and every real `C₀`, the [bolus AUC](bolus-auc.md)
`AUC(C₀) = C₀ * (Km + C₀ / 2) / Vmax` is the AUC of the linear one-compartment model with clearance
`CL = V * Vmax / Km` and volume `V` after the bolus dose `V * C₀`, plus a saturation term:
`AUC(C₀) = ∫₀^∞ C₀ * exp (-(Vmax / Km) * t) dt + C₀² / (2 * Vmax)`, where the linear AUC is
`D / CL = C₀ * Km / Vmax`. The identity holds for every real `C₀`; the reading as a dose and as
areas under concentration curves applies for `C₀ ≥ 0`.
