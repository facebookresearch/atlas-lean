# ℓ-graphs are suppressors of selection

**Setting.** Let $G$ be a connected undirected graph on $N$ vertices. In the birth–death Moran process each vertex holds a resident (fitness $1$) or a mutant (fitness $r > 0$); at each step a vertex is chosen to reproduce with probability proportional to fitness and its offspring replaces a uniformly chosen neighbour. One initial mutant is placed at a uniformly random vertex, and $\Phi_G(r)$ is the resulting probability of fixation. In the well-mixed population (the complete graph $K_N$),

$$\Phi_0(r) = \frac{1 - r^{-1}}{1 - r^{-N}} .$$

$G$ is an *amplifier of selection* if $\Phi_G(r) > \Phi_0(r)$ for all $r > 1$ and a *suppressor of selection* if $\Phi_G(r) < \Phi_0(r)$ for all $r > 1$ (the inequalities reverse for $r < 1$, and $\Phi_G(1) = 1/N$). Isothermal graphs, in which $T_i = \sum_{j \sim i} 1/d_j$ is constant, have $\Phi_G = \Phi_0$.

**ℓ-graphs.** For $n \ge 2$, the graph $\ell_{2n+2}$ is obtained from the complete graph $K_{2n}$ by splitting its vertices into two halves $H_1,H_2$ of $n$ vertices and adding two vertices $u_1,u_2$, where $u_i$ is joined to every vertex of $H_i$ and $u_1$ is joined to $u_2$.

**Theorem (computer-aided).** The graphs $\ell_6$, $\ell_8$ and $\ell_{10}$ are suppressors of selection: $\Phi_{\ell_N}(r) < \Phi_0(r)$ for all $r > 1$ and $\Phi_{\ell_N}(r) > \Phi_0(r)$ for all $0 < r < 1$, for $N = 6, 8, 10$.

## Depends on

- [Moran Fixation](../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)
- [Isothermal theorem, "if" direction](../../isothermal-theorem-for-evolutionary-graph-dynami/average-fixation-eq-moran-fixation.md)

## Expansion

$\Phi_G(r)$ solves a linear system over the $2^N$ mutant configurations, so it is a rational function $\Phi'(r)/\Phi''(r)$ whose numerator and denominator have degree bounded by about $2^N$. The symmetries of $\ell_N$ reduce the state space and bound the degrees by $d = N(N+1)/2 - 2$; normalizing the leading coefficients (since $\Phi \to 1$ as $r \to \infty$) leaves $2d$ unknown rational coefficients, fixed exactly by evaluating $\Phi$ symbolically at $2d$ fitness values ($r = 1,\dots,d+1$ and $r = 1/2,\dots,1/d$). The sign of $\Delta = \Phi_{\ell_N} - \Phi_0$ is then analysed on $r > 1$. An exhaustive numerical scan of all connected undirected graphs with at most $10$ vertices (fitness grid $0.25$ to $10$) found $\ell_6$ as the only suppressor of order $6$; Monte Carlo runs for $\ell_{12}$ and $\ell_{24}$ are consistent with the whole family being suppressors, with the effect vanishing as $N \to \infty$ under uniform initialization.

## Sources

- F. Alcalde Cuesta, P. González Sequeiros, Á. Lozano Rojo, "Suppressors of selection", PLoS ONE 12(7) (2017) e0180549, Eqs. (1) and (3), Results and Methods, <https://doi.org/10.1371/journal.pone.0180549>, PMCID PMC5503266.
