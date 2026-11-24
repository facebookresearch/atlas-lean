# Cylinder Temperature

Temperature profile of the steady solid cylinder with constant
conductivity `k` and uniform volumetric heat source `qvol`: at radius
`r` in a cylinder of radius `R` with surface temperature `Ts`,
`T(r) = Ts + qvol * (R^2 - r^2) / (4k)`. This is the regular polynomial
profile; at `r = 0` it is read through its polynomial extension, not by
evaluating a radial flux divided by `r`. Intended for `k ≠ 0`; the
physical profile is the restriction to `0 ≤ r ≤ R` with `0 < R`.
