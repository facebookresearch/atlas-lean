# Taylor remainder of the quadratic calibration about a base voltage

For a real coefficient $c_2$ and a real base voltage $v_0$, the remainder at a voltage $v$ is

$$
R_{v_0}(v) = c_2 (v - v_0)^2,
$$

in the output unit of the calibration. It is the exact remainder of the first-order part: for all
real $c_0$, $c_1$ and $v$ the [quadratic calibration](quad-calibration.md) is
$f(v) = L_{v_0}(v) + R_{v_0}(v)$, with $L_{v_0}$ the [first-order part](quad-linear-part.md)
([exact Taylor expansion](quad-calibration-eq-linear-add-remainder.md)). It depends on $c_2$ and
$v_0$ only, not on $c_0$ or $c_1$.
