# Totalized tangent-slope quotient

For a Weierstrass curve $W$ and any $x, y$,
`W.tangentSlope x y` is $(3x^2 + 2a_2x + a_4 - a_1y)/(2y + a_1x + a_3)$ with the division taken by
`Ring.inverse`, so the value is $0$ whenever $2y + a_1x + a_3$ is not a unit. Over a field with
$2y + a_1x + a_3 \ne 0$ it equals `W.toAffine.slope x x y y` (`tangentSlope_eq_slope`).

When $(x, y)$ is a point of $W$ and $2y + a_1x + a_3$ is a unit, the value is the slope of the
tangent line to $W$ at $(x, y)$. When $2y + a_1x + a_3 = 0$ the value $0$ is only the totalized
quotient. At a nonsingular point of $W$ over a field, $2y + a_1x + a_3$ is the partial derivative
in $y$ of the Weierstrass polynomial, so when it vanishes the partial derivative in $x$,
$a_1y - (3x^2 + 2a_2x + a_4)$, does not, and the tangent line is vertical: on $y^2 = x^3 - x$ at
$(0, 0)$ it is $x = 0$. At a singular point both partial derivatives vanish: on the cusp
$y^2 = x^3$ at $(0, 0)$ the tangent cone is the double line $y = 0$.
