# Integrated budget at equal rates

For all real `F`, `D`, `ka` and `t`, with the [depot amount](depot-amount.md)
`Ag(t) = D * exp (-ka * t)` and the [equal-rate central amount](central-amount-equal.md)
`Ac(t) = F * D * ka * t * exp (-ka * t)`,
`∫₀ᵗ (-(1 - F) * ka * Ag(s) - ka * Ac(s)) ds = (Ag(t) + Ac(t)) - (Ag(0) + Ac(0))`. For `t < 0` the
integral is oriented.
