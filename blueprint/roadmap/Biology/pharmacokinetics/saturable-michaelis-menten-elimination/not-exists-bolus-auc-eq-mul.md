# AUC is not proportional to dose

For `Vmax > 0` and every real `Km`, the [bolus AUC](bolus-auc.md)
`AUC(C₀) = C₀ * (Km + C₀ / 2) / Vmax` is not proportional to the initial concentration: there is no
constant `a` with `AUC(C₀) = a * C₀` for every `C₀ ≥ 0`. For `Km > 0`, where `AUC(C₀)` is the area
under the concentration curve, the AUC of saturable elimination is therefore not proportional to the
dose. For linear elimination, by contrast, the
[AUC `D / CL` is proportional to the dose](../one-compartment-linear-pharmacokinetics/integral-ici-concentration-bolus.md).
