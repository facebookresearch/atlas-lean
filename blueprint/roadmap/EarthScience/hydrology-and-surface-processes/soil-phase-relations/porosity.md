# Porosity of a soil element

For a soil (or other two-phase solid and void) element with solid volume `Vs` and void volume
`Vv`, both in the same volume unit, the porosity is the void fraction of the total volume,
`n = Vv / (Vs + Vv)`, a dimensionless number. It is defined for all real `Vs` and `Vv`: with the
convention `x / 0 = 0` it is `0` when `Vs + Vv = 0`. The intended domain is `Vs > 0` and `Vv ≥ 0`.
