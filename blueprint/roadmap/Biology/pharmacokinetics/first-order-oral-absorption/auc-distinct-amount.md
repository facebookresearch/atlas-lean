# Absorption AUC, distinct rates

For an absorption rate `ka > 0` and an elimination rate `k > 0` with `ka ≠ k`, and all real `F` and
`D`, the [distinct-rate central amount](central-amount.md)
`Ac(t) = F * D * ka * (exp (-k * t) - exp (-ka * t)) / (ka - k)` is integrable on `[0, ∞)` and
`∫₀^∞ Ac(t) dt = F * D / k`. Dividing by a volume `V > 0` gives the concentration AUC
`F * D / (k * V)`.
