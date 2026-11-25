# The Lyapunov derivative identity at an endemic equilibrium

Let $(a, c)$ be an [endemic equilibrium](is-endemic-eq.md) at coverage $p$, with $N \ne 0$, and let
$x, y \ne 0$. Then

$$
\Bigl(1 - \frac{a}{x}\Bigr) \Bigl(\frac{\beta ((1 - p) N - x)(x + y)}{N} - \gamma x\Bigr) +
\Bigl(1 - \frac{c}{y}\Bigr)
\Bigl(\frac{(1 - \varepsilon) \beta (p N - y)(x + y)}{N} - \gamma y\Bigr) = \dot V(x, y),
$$

the [Lyapunov derivative](lyapunov-deriv.md): the infected vector field with $S_u = (1 - p) N - x$
and $S_v = p N - y$, paired with the gradient of the [Lyapunov function](lyapunov.md).
