# First-order remainder of the vector calibration is exactly c2 δ²

For real coefficients $c_0$, $c_1$, $c_2$ and one-component real vectors $x = (x_0)$ and
$\delta = (\delta_0)$, let $r = F(x + \delta) - F(x) - DF(x)\,\delta$ be the first-order remainder
of the [one-component vector calibration](quad-calibration-vec.md) $F$ at $x$ in the direction
$\delta$, with $DF(x)$ the Fréchet derivative of $F$ at $x$. Its component is

$$
r_0 = c_2\,\bigl((x_0 + \delta_0) - x_0\bigr)^2 = c_2\,\delta_0^2,
$$

the [remainder](quad-remainder.md) of the quadratic calibration about the base voltage $x_0$,
evaluated at $x_0 + \delta_0$. As $F$ is differentiable everywhere, $DF(x)$ is its actual
derivative.
