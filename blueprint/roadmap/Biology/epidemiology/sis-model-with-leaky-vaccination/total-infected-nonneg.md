# The total infected stays nonnegative

For every [solution](is-solution.md) $(S_u, I_u, S_v, I_v)$ of the SIS model with leaky vaccination,
with transmission rate $\beta$, recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and
population size $N$, with $I_u(0) + I_v(0) \ge 0$, the total infected satisfies
$I_u(t) + I_v(t) \ge 0$ for every $t \ge 0$: it solves the linear equation $I' = k(t) I$ with
$k = \beta S_u / N + (1 - \varepsilon) \beta S_v / N - \gamma$. No condition on the parameters is
needed.
