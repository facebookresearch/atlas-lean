# Sign gvf Slope

Sign certificate for the gradually-varied-flow slope: for a
positive normal depth `yn` (rectangular Manning discharge `Q` at bed
slope `S0`) and a depth `y > 0` away from the critical depth
`yc = rectangularCriticalDepth (Q / b) g`, the declared slope has sign
`sign (y - yn) * sign (y - yc)`. Positive flow `0 < Q` follows from
`hyn` and is not a separate premise. The premise `y ≠ yc` keeps the
totalized value at the singular point out of the claim.
