# Derivative of the total amount with the canonical central amount

For all real `F`, `D`, `ka`, `k` and `t`, the total amount `Ag + Ac`, with the
[depot amount](depot-amount.md) `Ag(t) = D * exp (-ka * t)` and the
[canonical central amount](central-amount-canonical.md)
`Ac(t) = ∫₀ᵗ exp (-k * (t - s)) * (F * ka * D * exp (-ka * s)) ds`, has at `t` the derivative
`-(1 - F) * ka * Ag(t) - k * Ac(t)`; no distinct-rate condition is needed.
