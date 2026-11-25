# Temperature of a solid cylinder with a uniform heat source

For real `Ts`, `R`, `k`, `qvol` and `r`, the cylinder temperature is

`T(r) = Ts + qvol (R² - r²)/(4k)`,

the profile used for the steady temperature at radius `r` in a solid cylinder of radius `R` and
conductivity `k` with surface temperature `Ts` and uniform volumetric heat source `qvol`. It is the
regular polynomial profile, defined at `r = 0` by the same formula. It
[equals `Ts` at `r = R`](cylinder-temperature-surface.md), and for `k ≠ 0` its
[derivative](has-deriv-at-cylinder-temperature.md) is the [cylinder gradient](cylinder-gradient.md)
`-qvol r/(2k)`. It is intended for `k ≠ 0`; with `x/0 = 0` it is the constant `Ts` when `k = 0`. In
the physical reading `R > 0`, `k > 0` and `0 ≤ r ≤ R`.
