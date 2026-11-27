# Inlet-minus-outlet water volume balance

For a positive pore volume `φ * A * dx > 0`, one [physical step](sat-step.md) changes the water
volume `φ * A * dx * ∑ i, S i` of the cells `0, …, n` by the inlet water volume `Q * dt * f(s_in)`
minus the outlet water volume `Q * dt * f(s_out)`, where `s_in` and `s_out` are the
[normalized saturations](norm-sat.md) of the inflow saturation and of the outlet cell `S n`, and
`f` is the [fractional flow](frac-flow.md). The other arguments are any real numbers: with the
convention `x / 0 = 0`, every normalized saturation is `0` when `ΔS = 1 - Sor - Swc = 0`, and `f` is
`0` where its denominator vanishes.
