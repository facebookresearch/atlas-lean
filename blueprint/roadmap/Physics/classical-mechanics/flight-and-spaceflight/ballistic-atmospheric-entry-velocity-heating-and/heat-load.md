# Heat Load

The heat load `∫ q dt` over the finite horizon `[0, tf]`, `0 ≤ tf`, of a history
`t ↦ (ρ t, rn t, v t)` that stays in the validity box on the horizon. It is heat per unit area
(`J / m ^ 2` in SI units); the heat into a surface needs a declared area to multiply it. It is
the heat load only for an interval-integrable flux: otherwise Lean's integral is `0` by
convention, and the bounds below assume integrability.
