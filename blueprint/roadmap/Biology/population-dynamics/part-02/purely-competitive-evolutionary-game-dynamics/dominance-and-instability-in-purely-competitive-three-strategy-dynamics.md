# Dominance and instability in purely competitive three-strategy dynamics

An infinite population plays a $3$-strategy game with strictly positive payoff matrix $U = (u_{ij})$, $u_{ij} \neq u_{ji}$ for $i \neq j$. Each period every individual is paired at random with another; a pair of types $i,j$ produces two offspring that are both of type $i$ with probability proportional to $i$'s payoff in that pairing, $u_{ij}/(u_{ij} + u_{ji})$, and both of type $j$ otherwise (**purely competitive** or emulation dynamics: success depends only on head-to-head relative payoff). With the normalized matrix $\tilde u_{ij} = u_{ij}/(u_{ij} + u_{ji})$ (so $\tilde u_{ii} = \tfrac12$ and $\tilde u_{ij} + \tilde u_{ji} = 1$), the population state $\mathbf p_t \in \Delta^3$ evolves by

$$p_{i,t+1} = p_{i,t}^2 + 2\,p_{i,t}\sum_{j \neq i}\tilde u_{ij}\,p_{j,t} = 2\,p_{i,t}\,(\tilde U\mathbf p_t)_i, \qquad i = 1,2,3.$$

**Theorem.** Without mutation:

1. the pure states $\mathbf e_1, \mathbf e_2, \mathbf e_3$ are fixed points;
2. $\mathbf e_i$ is evolutionarily stable if and only if type $i$ is **dominant**, $\tilde u_{ij} > \tfrac12$ (equivalently $u_{ij} > u_{ji}$) for all $j \neq i$; in that case the pure states are the only fixed points and $\mathbf e_i$ is globally attracting;
3. if there is no dominant type and the pairwise contests are cyclic, $\tilde u_{12} > \tfrac12$, $\tilde u_{23} > \tfrac12$, $\tilde u_{13} < \tfrac12$ (type $1$ beats $2$, $2$ beats $3$, $3$ beats $1$), there is a unique non-pure fixed point, and it lies in the interior of the simplex;
4. any interior fixed point is unstable: arbitrarily close to it there are initial states whose orbits do not converge to it, and the population eventually cycles among neighbourhoods of the three pure states.

With a small probability $\mu$ that each offspring mutates to one of the other two types, a dominant type keeps a globally attracting fixed point near its pure state, while in the cyclic case the interior fixed point undergoes a supercritical Hopf bifurcation and becomes globally attracting above a typically small critical mutation rate, so weak mutation stabilizes rock–paper–scissors-like competition.

## Expansion

Because $\tilde u_{ii} = \tfrac12$ and $\tilde u_{ij} + \tilde u_{ji} = 1$, the map preserves the simplex: $\sum_i 2p_i(\tilde U\mathbf p)_i = \sum_i p_i^2 + \sum_{i\neq j}p_ip_j = 1$. If type $1$ is dominant, $p_{1,t+1} = p_{1,t}(p_{1,t} + 2\tilde u_{12}p_{2,t} + 2\tilde u_{13}p_{3,t}) \ge p_{1,t}(p_{1,t} + p_{2,t} + p_{3,t}) = p_{1,t}$ with equality only at pure states, so $p_1$ increases strictly to $1$ from every state other than $\mathbf e_2, \mathbf e_3$. Conversely, if $\tilde u_{12} < \tfrac12$, on the edge between $\mathbf e_1$ and $\mathbf e_2$ the share of type $1$ strictly decreases, so $\mathbf e_1$ is invadable. In the cyclic case the fixed-point equations $(\tilde U\mathbf p)_i = \tfrac12$ form a linear system with a unique positive solution. Eliminating $p_3$ gives a planar map whose Jacobian at the interior fixed point has eigenvalues $1 \pm i\sqrt{\omega}$ with $\omega > 0$ explicit in the $\tilde u_{ij}$; their modulus exceeds $1$, so the fixed point is an unstable focus.

## Sources

- Carl Veller, Vinesh Rajpaul, "Purely competitive evolutionary dynamics for games", arXiv (2012). Section 2 (model and interpretations), Section 3 (normalization $\tilde U$, stage-to-stage dynamics, Theorems 1–4), Section 4 (mutations: feasible fixed points and stability). <https://doi.org/10.48550/arXiv.1208.2583>. Published version: Physical Review E 86(4) (2012), article 041907, <https://doi.org/10.1103/physreve.86.041907>; locators above refer to the arXiv version.
