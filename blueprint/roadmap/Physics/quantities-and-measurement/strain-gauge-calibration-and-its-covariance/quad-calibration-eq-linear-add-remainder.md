# Exact first-order Taylor expansion of the quadratic calibration

For all real coefficients $c_0$, $c_1$, $c_2$, every base voltage $v_0$ and every voltage $v$, the
[quadratic calibration](quad-calibration.md) is its [first-order part](quad-linear-part.md) at $v_0$
plus the [remainder](quad-remainder.md), with no term dropped:

$$
c_0 + c_1 v + c_2 v^2
= \bigl(c_0 + c_1 v_0 + c_2 v_0^2\bigr) + (c_1 + 2 c_2 v_0)(v - v_0) + c_2 (v - v_0)^2.
$$
