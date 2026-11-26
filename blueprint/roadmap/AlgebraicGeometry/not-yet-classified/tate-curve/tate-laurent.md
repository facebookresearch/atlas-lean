# The Tate curve over Laurent series

The base change of `tatePowerSeries` along
`laurentOfInt K`: the Weierstrass curve `y² + xy = x³ + a₄(q)x + a₆(q)` over the Laurent series
ring `K((q))`. Its Laurent variable is the same `q`, now invertible; it is not the local parameter
`T` of `tateOriginX`. The discriminant of `tatePowerSeries` is `q` times a unit of `ℤ⟦q⟧`, so here
it is a unit, and the curve is elliptic for every commutative ring `K`
(`instIsElliptic_tateLaurent`).
