# The moment as minus the stiffness times the second iterated derivative

For all real `w`, `EI`, `L` and `x`, the [bending moment](uniform-beam-moment.md)
`M(x) = -EI * y''(x)`, defined through the derivative of the derivative of the
[uniform-load deflection](uniform-load-deflection.md)
`y(x) = w * (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4) / (24 * EI)`, equals `-EI` times the second iterated
derivative of `y` at `x`: the two ways of writing `y''` agree.
