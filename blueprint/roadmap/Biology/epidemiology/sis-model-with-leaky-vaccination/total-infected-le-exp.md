# Exponential bound on the total infected

Let $\beta \ge 0$, $\gamma > 0$, $0 \le \varepsilon \le 1$ and $N > 0$, and let
$(S_u, I_u, S_v, I_v)$ be a [solution](is-solution.md) of the SIS model with leaky vaccination, with
transmission rate $\beta$, recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population
size $N$, with group sizes $S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$ and all four
classes nonnegative at time $0$. Then for every $t \ge 0$, with the
[vaccinated reproduction number](rv.md) $R_v = (\beta / \gamma)(1 - \varepsilon p)$ (any value),

$$I_u(t) + I_v(t) \le \bigl(I_u(0) + I_v(0)\bigr)\, e^{-\gamma (1 - R_v) t}.$$

When $R_v < 1$ this is exponential decay.
