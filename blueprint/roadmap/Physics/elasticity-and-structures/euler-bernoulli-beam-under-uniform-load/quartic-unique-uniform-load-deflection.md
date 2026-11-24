# A quartic with the beam conditions equals the deflection function

Let `EI ≠ 0` and `L ≠ 0`, and let the [quartic](quartic-fun.md)
`p(x) = a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e` satisfy `24 * a * EI = w`, `p(0) = 0`,
`p(L) = 0`, `2 * c = 0` and `12 * a * L ^ 2 + 6 * b * L + 2 * c = 0` (the beam equation and the
simple-support conditions, as for the [uniqueness in the quartic class](quartic-unique.md)). Then
`p(x)` equals the [uniform-load deflection](uniform-load-deflection.md)
`y(x) = w * (L ^ 3 * x - 2 * L * x ^ 3 + x ^ 4) / (24 * EI)` at every real `x`.
