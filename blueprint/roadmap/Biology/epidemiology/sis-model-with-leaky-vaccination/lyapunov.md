# Lyapunov function of the endemic equilibrium

For real $a$, $c$, $x$ and $y$, the Lyapunov function of the endemic equilibrium $(a, c)$ is

$$V(x, y) = g(a, x) + g(c, y), \qquad g(a, x) = x - a - a \log\frac{x}{a},$$

with the [Volterra function](../global-stability-of-the-seir-model/volterra.md) $g$, the real
logarithm ($\log 0 = 0$, $\log z = \log |z|$ for $z < 0$) and the convention $z / 0 = 0$. For
$a, c, x, y > 0$ each term is nonnegative and vanishes only at $x = a$, respectively $y = c$.
