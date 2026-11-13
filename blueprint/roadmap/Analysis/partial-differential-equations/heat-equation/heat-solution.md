# Heat-kernel solution

For $f\colon \mathbb{R} \to \mathbb{R}$, the heat solution
$u(t, x)$ of $f$ is given for $t > 0$ by

$$u(t, x) = (4 \pi t)^{-1/2} \int_{\mathbb{R}} e^{-(x - y)^2/(4t)} f(y) \, dy$$

and by $u(t, x) = f(x)$ for $t \le 0$.

The integral is the Lebesgue integral, taken to be $0$ when the integrand is not integrable. The
value for $t \le 0$ only makes $u$ defined for all real $t$ and $x$; the heat equation statement
constrains $u$ only for $t > 0$.
