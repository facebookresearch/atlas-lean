# Bulk unit weight from the soil phase relations

For a soil element with specific gravity of solids `Gs`, degree of saturation `S`, void ratio `e`
and water unit weight `γw`, the bulk unit weight, total weight over total volume, is
`γ = (Gs + S * e) * γw / (1 + e)`. It is defined for all real arguments: with the convention
`x / 0 = 0` it is `0` when `e = -1`. The intended domain is `Gs > 0`, `0 ≤ S ≤ 1`, `e ≥ 0` and
`γw > 0`.
