# First-order Taylor part of the quadratic calibration

For real coefficients $c_0$, $c_1$, $c_2$ and a real base voltage $v_0$, the first-order part of the
[quadratic calibration](quad-calibration.md) $f(v) = c_0 + c_1 v + c_2 v^2$ at $v_0$ is the affine
function

$$
L_{v_0}(v) = f(v_0) + (c_1 + 2 c_2 v_0)(v - v_0),
$$

where $c_1 + 2 c_2 v_0 = f'(v_0)$ is the derivative of $f$ at $v_0$
([derivative of the quadratic calibration](quad-calibration-has-deriv-at.md)). The difference
$f - L_{v_0}$ is the [remainder](quad-remainder.md) $c_2 (v - v_0)^2$
([exact Taylor expansion](quad-calibration-eq-linear-add-remainder.md)).
