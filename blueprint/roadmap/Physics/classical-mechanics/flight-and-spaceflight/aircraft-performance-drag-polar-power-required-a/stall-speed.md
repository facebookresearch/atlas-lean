# Stall Speed

Stall speed `V_s = √(2 * W / (ρ * S * CLmax))` for the polar's maximum lift coefficient
`CLmax`. The physical regime is `W, ρ, S, CLmax > 0`; for `W ≤ 0` the radicand is not positive
and `Real.sqrt` returns the meaningless value `0`, so the stall results assume `0 < W`.
