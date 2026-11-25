# For β > 0 and 0 < ε < 1, below the critical coverage, infections in both groups become endemic

Let $\beta, \gamma, N > 0$, $0 < \varepsilon < 1$ and $0 < p < 1$, with $p < p_c$ for the
[critical coverage](critical-coverage.md) $p_c = (1 - \gamma / \beta) / \varepsilon$. Then every
[solution](is-solution.md) $(S_u, I_u, S_v, I_v)$ of the SIS model with leaky vaccination, with
transmission rate $\beta$, recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population
size $N$, with group sizes $S_u(0) + I_u(0) = (1 - p) N$ and $S_v(0) + I_v(0) = p N$,
$S_u(0), S_v(0) \ge 0$ and $I_u(0), I_v(0) > 0$, tends to an [endemic equilibrium](is-endemic-eq.md)
$(a, c)$ at coverage $p$: $S_u(t) \to (1 - p) N - a$, $I_u(t) \to a$, $S_v(t) \to p N - c$ and
$I_v(t) \to c$ as $t \to \infty$. By [uniqueness](unique.md), $(a, c)$ is the same for every such
solution.
