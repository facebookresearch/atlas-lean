# With an endemic equilibrium and infectives in both groups, Iᵤ stays bounded away from zero

Let $\beta \ge 0$, $\gamma > 0$, $\varepsilon < 1$ and $N > 0$, let $(a, c)$ be an
[endemic equilibrium](is-endemic-eq.md) at coverage $p$, and let $(S_u, I_u, S_v, I_v)$ be a
[solution](is-solution.md) of the SIS model with leaky vaccination, with transmission rate $\beta$,
recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population size $N$, with group sizes
$S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$, $S_u(0), S_v(0) \ge 0$ and
$I_u(0), I_v(0) > 0$. With the [Lyapunov function](lyapunov.md) $V(x, y) = g(a, x) + g(c, y)$, with
the [Volterra function](../global-stability-of-the-seir-model/volterra.md)
$g(a, x) = x - a - a \log(x / a)$ and $V(0) = V(I_u(0), I_v(0))$, for every $t \ge 0$

$$I_u(t) \ge a\, e^{-(V(0) + a) / a} > 0.$$

The bound depends on the solution through $V(0)$.
