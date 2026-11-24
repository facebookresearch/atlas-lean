# The canonical central amount solves the central equation

For all real `F`, `D`, `ka`, `k` and `s`, the
[canonical central amount](central-amount-canonical.md)
`Ac(t) = ∫₀ᵗ exp (-k * (t - s)) * (F * ka * D * exp (-ka * s)) ds` is differentiable at `s` with
derivative `F * ka * Ag(s) - k * Ac(s)`, where `Ag(s) = D * exp (-ka * s)` is the
[depot amount](depot-amount.md).
