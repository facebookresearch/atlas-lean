# Pointwise remainder bound for the quadratic calibration on an interval

Let $a$, $b$, $c_0$, $c_1$ and $c_2$ be real, and let $x = (x_0)$ and $\delta = (\delta_0)$ be
one-component real vectors with $x_0$ and $x_0 + \delta_0$ in the voltage interval $[a, b]$. The
first-order remainder $r = F(x + \delta) - F(x) - DF(x)\,\delta$ of the
[one-component vector calibration](quad-calibration-vec.md) $F$, with $DF(x)$ its Fréchet derivative
at $x$, satisfies

$$
|r_0| \le \frac{2\,|c_2|}{2}\,\|\delta\|^2 = |c_2|\,\delta_0^2,
$$

where $\|\delta\| = |\delta_0|$ is the sup norm. This is the componentwise remainder bound from a
Hessian bound
([remainder bound from a Hessian bound](../covariance-propagation-and-lipschitz-error-bound/jacobian-remainder-component-le-of-hessi.md))
with the [Hessian bound](quad-calibration-vec-hessian-le.md) $2\,|c_2|$. By the
[exact remainder](quad-calibration-vec-jacobian-remainder.md) $r_0 = c_2\,\delta_0^2$ it holds with
equality. It bounds the remainder at each pair of points; it is not a statement about the moments of
the remainder under a distribution of voltages.
