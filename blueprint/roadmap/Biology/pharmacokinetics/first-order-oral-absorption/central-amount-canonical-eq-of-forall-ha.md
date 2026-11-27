# A solution of the central equation from zero is the canonical amount

For all real `F`, `D`, `ka` and `k`, let `y` be differentiable at every real time `t` with
`y'(t) = F * ka * D * exp (-ka * t) - k * y(t)` and `y(0) = 0`. Then `y(t)` equals the
[canonical central amount](central-amount-canonical.md)
`Ac(t) = ∫₀ᵗ exp (-k * (t - s)) * (F * ka * D * exp (-ka * s)) ds` at every real `t`: the
difference, multiplied by the exponential factor `exp (k * t)`, has derivative zero.
