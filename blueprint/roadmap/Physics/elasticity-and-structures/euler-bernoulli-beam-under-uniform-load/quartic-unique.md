# A quartic with the beam conditions is the uniform-load deflection

Let `EI ≠ 0` and `L ≠ 0`, and let the [quartic](quartic-fun.md)
`p(x) = a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e` satisfy `24 * a * EI = w` (so that
`EI * p'''' = w`), `p(0) = 0`, `p(L) = 0`, and the vanishing of its second derivatives at the
supports, `p''(0) = 2 * c = 0` and `p''(L) = 12 * a * L ^ 2 + 6 * b * L + 2 * c = 0`. Then for every
real `x`, `p(x) = w * x * (L ^ 3 - 2 * L * x ^ 2 + x ^ 3) / (24 * EI)`, the simply supported
uniform-load deflection.

In terms of the [uniform-load deflection](uniform-load-deflection.md) `y`, this says `p(x) = y(x)`
at every real `x`.
