# Boundary attraction and strict Nash stability of the stochastic replicator dynamics with jumps

**Model.** Subpopulation $i \in \{1,\dots,n\}$, playing pure strategy $S_i$ against payoff matrix $A = (a_{ij})$, has size

$$dr_i(t) = r_i(t-)\Big((A\mathbf s(t-))_i\,dt + \sigma_i\,dW_i(t) + \int_{\mathbb R} h_i(x)\,\tilde N(dt,dx)\Big),$$

where $W_i$ are independent Brownian motions, $\tilde N$ is a compensated Poisson random measure with finite Lévy measure $\nu$ modelling anomalous events of strength $x$, and the jump functions $h_i$ are bounded, $C^1$, with $\inf_x h_i(x) > -1$. The strategy frequencies $s_i = r_i/\sum_j r_j$ then satisfy the **extended stochastic replicator dynamics**

$$d\mathbf s = D^1(\mathbf s)\,dt + D^2(\mathbf s)\,d\mathbf W + \int_{\mathbb R} D^3(\mathbf s)\,\tilde N(dt,dx),$$

$$D^1(\mathbf y) = \big[\mathrm{diag}(\mathbf y) - \mathbf y\mathbf y^\top\big]\big[A - \mathrm{diag}(\sigma_1^2,\dots,\sigma_n^2)\big]\mathbf y + \int_{\mathbb R}\Big(\mathbf y\mathbf h^\top - \mathrm{diag}(\mathbf h) + \frac{\mathrm{diag}(1+\mathbf h) }{1 + \mathbf y^\top\mathbf h} - I\Big)\mathbf y\,\nu(dx),$$

$$D^2(\mathbf y) = \big[\mathrm{diag}(\mathbf y) - \mathbf y\mathbf y^\top\big]\mathrm{diag}(\sigma_i), \qquad D^3(\mathbf y) = \Big(\frac{\mathrm{diag}(1+\mathbf h(x))}{1 + \mathbf y^\top\mathbf h(x)} - I\Big)\mathbf y.$$

The simplex $\Delta_n$ is invariant almost surely for all finite times, and its only stationary points are the vertices.

**Theorem.**

1. For any payoff matrix and $\varepsilon > 0$, let $\tau_\varepsilon = \inf\{t > 0 : s_k(t) \ge 1-\varepsilon \text{ for some } k\}$. Then $\mathbb E_{\mathbf y}[\tau_\varepsilon^m] < \infty$ for all $m \in \mathbb N$ and

$$\mathbb P_{\mathbf y}\Big(\sup_{t>0}\max_k s_k(t) = 1\Big) = 1 \qquad (\mathbf y \in \Delta_n).$$

2. (*Stochastically stable strict Nash equilibria.*) Let $S_k$ be a strict Nash equilibrium with $a_{kk} > a_{jk} + \sigma_k^2$ for all $j \ne k$, and suppose the jump functions are nonnegative and satisfy the paper's sign conditions on jump integrals (Assumption 4.1). Then

$$\mathbb P_{\mathbf y}\Big(\lim_{t\to\infty}\mathbf s(t) = \mathbf e_k\Big) \ge y_k,$$

without restricting $\mathbf y$ to a neighborhood of $\mathbf e_k$; under the alternative condition of Corollary 4.1, for every $\varepsilon > 0$ there is a neighborhood $U$ of $\mathbf e_k$ with $\mathbb P_{\mathbf y}(\lim_t\mathbf s(t) = \mathbf e_k) \ge 1-\varepsilon$ for $\mathbf y \in U$.

Analogous results give extinction of strictly dominated pure strategies and positive recurrence near an interior evolutionarily stable strategy, extending Imhof's results for Brownian noise to Lévy jump noise.

## Depends on

- [Solutions of the replicator equation](../../../replicator-dynamics/is-solution.md)

## Expansion

Item 1 uses a Lyapunov-type function of $\mathbf s$ whose generator, including the nonlocal jump part, is bounded above by a negative constant away from the vertices, so the hitting time of an $\varepsilon$-neighborhood of the boundary vertices has finite moments. For item 2, $V(\mathbf y) = y_k^{-\alpha}$-type functions (or $\log y_k$) are supermartingales near $\mathbf e_k$ when the payoff advantage of $S_k$ exceeds its own noise variance and the compensated jumps do not push mass away from $S_k$ on average; positivity of the jump functions lets the jump integrals be bounded uniformly, which removes the neighborhood restriction of the purely diffusive case.

## Sources

- Andrew Vlasic, "Long-run analysis of the stochastic replicator dynamics in the presence of random jumps", arXiv (2012). Section 2 (model, Assumption 2.1, Proposition 2.1), Section 3 (Theorem 3.1, two-strategy case), Section 4 (Theorems 4.1–4.2, Corollary 4.1, Assumption 4.1). <https://doi.org/10.48550/arXiv.1206.0344>. Published version: Journal of Dynamics and Games 5(4) (2018), 283–309, <https://doi.org/10.3934/jdg.2018018>; locators above refer to the arXiv version.
