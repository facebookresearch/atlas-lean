# Elastic first-yield moment of a rectangular section

For all real `b`, `h` and `σy`, the [bending moment](section-moment.md) of the
[first-yield stress](first-yield-stress.md) is
`∫_{-h/2}^{h/2} y * (b * σy * (2 * y / h)) dy = σy * b * h ^ 2 / 6`, the yield stress times the
elastic section modulus `b * h ^ 2 / 6`. At `h = 0` both sides are `0` (the distribution is `0` by
the convention `x / 0 = 0`). The physical reading is `b > 0`, `h > 0` and `σy > 0`.
