# Tangent slope, totalized

For a Weierstrass curve $W$ and $x, y$, `W.tangentSlope x y` is
$(3x^2 + 2a_2x + a_4 - a_1y)/(2y + a_1x + a_3)$, the slope of the tangent line at $(x, y)$, with
the division taken by `Ring.inverse`: the value is $0$ when $2y + a_1x + a_3$ is not a unit. Over a
field with $2y + a_1x + a_3 \ne 0$ it is `W.toAffine.slope x x y y` (`tangentSlope_eq_slope`).
