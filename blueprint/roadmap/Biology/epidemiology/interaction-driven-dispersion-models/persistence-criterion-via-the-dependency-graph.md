# Persistence criterion via the dependency graph

**Setting.** Consider an [interaction-driven dispersion model](convergence-with-an-acyclic-transition-graph.md) $\dot y_i = I_i - O_i$ with acyclic transition graph, so that every $y_i(t)$ converges. The **dependency graph** has an arc $u \to v$ (self-loops allowed) whenever $\beta^u_{uv} > 0$, that is, whenever agents leave state $u$ through encounters with state $v$. A state is **vanishing** if $\lim_t y_i(t) = 0$ and **persistent** if the limit is positive. Assume (DAG$^{-}$) that every cycle of the dependency graph contains a state with a persistent dependency successor.

**Statement.** Suppose the transition graph is acyclic and the DAG$^{-}$ assumption holds.

1. Every vanishing state has finite integral: $\int_0^\infty y_i(t)\,dt < \infty$.
2. A state $i$ is persistent if and only if all of its dependency successors are vanishing: $\lim_t y_i(t) > 0 \iff \lim_t y_j(t) = 0$ for every $j$ with $\beta^i_{ij} > 0$.
3. If, in each cycle of the dependency graph, a state with a persistent dependency successor can be identified, the model has the same asymptotic characterization as a model with the same transition graph and an acyclic dependency graph. Then the vanishing/persistent label of every state is determined recursively by item 2, and it depends neither on the initial fractions in $(0,1)$ nor on the values of the $\beta$ coefficients, only on which of them are nonzero.

Without the DAG$^{-}$ assumption the conclusions can fail: for $\dot y_1 = -\alpha_1 y_1 y_2$, $\dot y_2 = -\alpha_2 y_2 y_3$, $\dot y_3 = -\alpha_3 y_3 y_1$, $\dot y_4 = \alpha_1 y_1 y_2 + \alpha_2 y_2 y_3 + \alpha_3 y_3 y_1$ with $\alpha_i > 0$ (a three-cycle in the dependency graph draining into state 4), all three cycle states vanish, yet $\max\{y_1, y_2, y_3\} \ge 1/(ct + k)$, so their integrals diverge.

## Depends on

- [Convergence of interaction-driven dispersion models with acyclic transitions](convergence-with-an-acyclic-transition-graph.md)

## Expansion

Since $O_i = y_i \sum_j \beta^i_{ij} y_j \to 0$, a persistent state forces $\sum_j \beta^i_{ij} y_j \to 0$, so all its dependency successors vanish. Conversely, if every dependency successor $j$ of $i$ vanishes with $\int_0^\infty y_j < \infty$, the per-capita exit rate of $i$ is integrable, and $y_i$ is bounded below by $y_i(0)\exp\!\big(-\int_0^\infty \sum_j \beta^i_{ij} y_j\big) > 0$. Integrability of vanishing states comes from a persistent successor: if $y_i \to 0$ some dependency successor $m$ of $i$ stays positive, and then $\int_0^\infty y_i\,y_m < \infty$ gives $\int_0^\infty y_i < \infty$; the DAG$^{-}$ assumption makes this induction well founded around cycles.

## Sources

- K. M. D. Chan, D. T. Crommelin and M. R. H. Mandjes, Asymptotic behavior for a general class of spreading models, arXiv (2025). <https://doi.org/10.48550/arXiv.2511.02437> (Theorems 2 and 3, Proposition 1, Corollary 1, Assumption 2, Definitions 7 and 8; counterexample Propositions 2 and 3.)
