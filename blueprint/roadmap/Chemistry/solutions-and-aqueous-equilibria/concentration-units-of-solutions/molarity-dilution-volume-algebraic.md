# Molarity dilution Volume algebraic

An algebraic identity, not a physical claim: for `c₁ * V₁ ≠ 0` and every `c₂`,
`(c₁ * V₁) / (c₁ * V₁ / c₂) = c₂`, i.e. `molarity (c₁ * V₁) (dilutionVolume c₁ V₁ c₂) = c₂`.
At `c₂ = 0` the computed volume is `0` and the identity holds only through Lean's `x / 0 = 0`.
For the physical statement see `dilutionVolume_dilutes`.
