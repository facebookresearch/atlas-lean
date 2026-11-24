# Isothermal Density band bounds fail outside

The band bounds do not extend beyond the band: below `z₁` the density exceeds the upper
bound `ρ0 * exp (-z₁ / H)`, and above `z₂` it falls below the lower bound
`ρ0 * exp (-z₂ / H)`. The band hypothesis of `isothermalDensity_band_bounds` cannot be
dropped.
