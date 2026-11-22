# Ideal Gas Entropy Change adiabatic

Reversible-adiabatic case: for positive temperatures and volumes, if
`T₂ / T₁ = (V₁ / V₂) ^ (R / cv)` (the adiabatic relation for constant `cv`) then `ΔS = 0`.
Route: `Real.log` algebra (`Real.log_div`, `Real.log_rpow`), then `field_simp` and `ring`.
