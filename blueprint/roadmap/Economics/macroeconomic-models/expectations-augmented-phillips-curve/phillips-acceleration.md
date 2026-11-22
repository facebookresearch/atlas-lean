# Accelerationist form (MA06.T03)

If the unemployment gap is constant,
`u (t + 1) - uₙ = g` for every `t`, then inflation falls (or rises) linearly:
`π t = π 0 - t * (κ * g)`. Inflation is then a unit-root affine recurrence, so this is
`MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_add_nsmul_of_one` with intercept `-(κ * g)`.
