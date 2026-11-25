# Scaled state matrix of the ideal buck converter

For real numbers `L`, `C`, `R`, `Iref` and `Vref`, the scaled state matrix `Ã` has rows
`(0, -Vref / (L Iref))` and `(Iref / (C Vref), -1 / (R C))`, with `a / 0 = 0`. For nonzero `Iref`
and `Vref` it satisfies [`S Ã = A S`](state-scaling-mul-scaled-buck-matrix.md), so `Ã = S⁻¹ A S` for
the [state matrix](buck-matrix.md) `A` and the [state scaling](state-scaling.md) `S`.
