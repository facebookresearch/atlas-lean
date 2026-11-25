# With infectives in both groups, the Lyapunov function never exceeds its initial value

Let $\beta \ge 0$, $\gamma > 0$, $\varepsilon < 1$ and $N > 0$, let $(a, c)$ be an
[endemic equilibrium](is-endemic-eq.md) at coverage $p$, and let $(S_u, I_u, S_v, I_v)$ be a
[solution](is-solution.md) of the SIS model with leaky vaccination, with transmission rate $\beta$,
recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population size $N$, with group sizes
$S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$, $S_u(0), S_v(0) \ge 0$ and
$I_u(0), I_v(0) > 0$. With the [Lyapunov function](lyapunov.md) $V(x, y) = g(a, x) + g(c, y)$, with
the [Volterra function](../global-stability-of-the-seir-model/volterra.md)
$g(a, x) = x - a - a \log(x / a)$, for every $t \ge 0$

$$V\bigl(I_u(t), I_v(t)\bigr) \le V\bigl(I_u(0), I_v(0)\bigr).$$
