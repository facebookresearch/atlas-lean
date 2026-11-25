# Integrated budget at distinct rates

For distinct rates `ka ≠ k` and all real `F`, `D` and `t`, with the [depot amount](depot-amount.md)
`Ag(t) = D * exp (-ka * t)` and the [distinct-rate central amount](central-amount.md)
`Ac(t) = F * D * ka * (exp (-k * t) - exp (-ka * t)) / (ka - k)`,
`∫₀ᵗ (-(1 - F) * ka * Ag(s) - k * Ac(s)) ds = (Ag(t) + Ac(t)) - (Ag(0) + Ac(0))`: the change in
total amount is the integral of the two loss terms. For `t < 0` the integral is oriented.
