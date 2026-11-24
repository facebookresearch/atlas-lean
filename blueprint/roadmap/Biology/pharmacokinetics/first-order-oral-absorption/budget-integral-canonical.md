# Integrated budget with the canonical central amount

For all real `F`, `D`, `ka`, `k` and `t`, with the [depot amount](depot-amount.md)
`Ag(t) = D * exp (-ka * t)` and the [canonical central amount](central-amount-canonical.md)
`Ac(t) = ∫₀ᵗ exp (-k * (t - s)) * (F * ka * D * exp (-ka * s)) ds`,
`∫₀ᵗ (-(1 - F) * ka * Ag(s) - k * Ac(s)) ds = (Ag(t) + Ac(t)) - (Ag(0) + Ac(0))`. For `t < 0` the
integral is oriented.
