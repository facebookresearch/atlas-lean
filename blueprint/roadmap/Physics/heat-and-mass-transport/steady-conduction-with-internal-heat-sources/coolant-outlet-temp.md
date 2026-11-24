# Coolant Outlet Temp

Coolant outlet temperature `Tout = Tin + 2 q₀ Lₑ sin (π L / (2 Lₑ)) / (π ṁ cp)`. Intended for
`ṁ > 0` and `cp > 0`; at `ṁ = 0` Lean's `x / 0 = 0` gives the junk value `Tin`, while blocked flow
has no steady state (`fixture_blocked_flow`).
