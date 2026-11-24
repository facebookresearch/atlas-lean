# The Lyapunov derivative along solutions

Let $(a, c)$ be an [endemic equilibrium](is-endemic-eq.md) at coverage $p$, with $N \ne 0$, and let
$(S_u, I_u, S_v, I_v)$ be a [solution](is-solution.md) of the SIS model with leaky vaccination, with
transmission rate $\beta$, recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population
size $N$, with group sizes $S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$. At every
$t \ge 0$ with $I_u(t) > 0$ and $I_v(t) > 0$, the map $s \mapsto V(I_u(s), I_v(s))$, with $V$ the
[Lyapunov function](lyapunov.md), has derivative $\dot V(I_u(t), I_v(t))$, the
[Lyapunov derivative](lyapunov-deriv.md).
