# For q₀ ≥ 0 the clad is at most the outlet temperature plus q₀ over h P

Let `ṁ > 0`, `cp > 0`, `q₀ ≥ 0`, `0 < L ≤ Lₑ`, `h > 0` and `P > 0`, and let `T` be a
[steady coolant profile](is-steady-coolant-profile.md) with inlet value `T_in`. If the clad surface
temperature `T_clad` obeys the prescribed film law `h P (T_clad(z) - T(z)) = q′(z)` for
`-L/2 ≤ z ≤ L/2`, with film coefficient `h` and heated perimeter `P`, then on the same range

`T_clad(z) ≤ T_out + q₀/(hP)`,

with the [outlet temperature](coolant-outlet-temp.md) `T_out = T_in + 2q₀Lₑ sin(πL/(2Lₑ))/(π ṁ cp)`.
