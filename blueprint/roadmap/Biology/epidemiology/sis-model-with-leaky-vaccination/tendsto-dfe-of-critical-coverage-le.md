# For 0 < ε < 1, reaching the critical coverage clears the infection

Let $\beta \ge 0$, $\gamma > 0$, $0 \le \varepsilon \le 1$ and $N > 0$, and let
$(S_u, I_u, S_v, I_v)$ be a [solution](is-solution.md) of the SIS model with leaky vaccination, with
transmission rate $\beta$, recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population
size $N$, with group sizes $S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$ and all four
classes nonnegative at time $0$. If $\beta > 0$, $0 < \varepsilon < 1$ and $p \ge p_c$ for the
[critical coverage](critical-coverage.md) $p_c = (1 - \gamma / \beta) / \varepsilon$, then
$I_u(t) \to 0$, $I_v(t) \to 0$, $S_u(t) \to (1 - p) N$ and $S_v(t) \to p N$ as $t \to \infty$.
