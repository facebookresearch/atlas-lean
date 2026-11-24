# Lyapunov stability of the endemic equilibrium

Let $\beta \ge 0$, $\gamma > 0$, $\varepsilon < 1$ and $N > 0$, let $(a, c)$ be an
[endemic equilibrium](is-endemic-eq.md) at coverage $p$, and let $(S_u, I_u, S_v, I_v)$ be a
[solution](is-solution.md) of the SIS model with leaky vaccination, with transmission rate $\beta$,
recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population size $N$, with group sizes
$S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$, $S_u(0), S_v(0) \ge 0$ and
$I_u(0), I_v(0) > 0$. Then for every $t \ge 0$

$$
(I_u(t) - a)^2 + (I_v(t) - c)^2 \le
2 N \Bigl(\frac{(I_u(0) - a)^2}{I_u(0)} + \frac{(I_v(0) - c)^2}{I_v(0)}\Bigr).
$$
