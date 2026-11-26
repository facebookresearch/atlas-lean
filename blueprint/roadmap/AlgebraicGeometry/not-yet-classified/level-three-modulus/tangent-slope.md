# Totalized tangent-slope quotient

For a Weierstrass curve $W$ and $x, y$,
`W.tangentSlope x y` is $(3x^2 + 2a_2x + a_4 - a_1y)/(2y + a_1x + a_3)$ with the division taken by
`Ring.inverse`, so the value is $0$ whenever $2y + a_1x + a_3$ is not a unit. When $(x, y)$ is a
point of $W$ and $2y + a_1x + a_3$ is a unit, it is the slope of the tangent line to $W$ at
$(x, y)$. At a point of $W$ where $2y + a_1x + a_3 = 0$ the tangent line is vertical and the
value $0$ is not its slope: on $y^2 = x^3 - x$ at $(0, 0)$ the tangent line is $x = 0$. Over a
field with $2y + a_1x + a_3 \ne 0$ it equals `W.toAffine.slope x x y y`
(`tangentSlope_eq_slope`).
