# Dilution Volume

The computed final volume `V₂ = c₁ * V₁ / c₂` for diluting from `c₁, V₁` to the target
concentration `c₂`. For positive `c₁`, `V₁` and a target `0 < c₂ ≤ c₁` it is at least `V₁` and
achieves the target (`dilutionVolume_dilutes`). This pins the dilution-volume convention; no
Mathlib definition provides it (Loogle finds no `dilutionVolume`).
