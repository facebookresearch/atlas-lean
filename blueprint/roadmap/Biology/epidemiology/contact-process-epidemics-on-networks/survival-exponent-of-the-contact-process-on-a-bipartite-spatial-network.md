# Survival exponent of the contact process on a bipartite spatial network

**Network.** Let $\mathcal P_1, \mathcal P_2 \subset \mathbb{R} \times [0,1]$ be independent unit-intensity Poisson processes ("type 1" and "type 2" vertices, e.g. people and places), with an extra type-1 root $o$ at $(0, U)$, $U \sim \mathrm{Unif}(0,1)$. For $\gamma_1, \gamma_2 \in (0,1)$, join $(x,u) \in \mathcal P_1$ and $(y,v) \in \mathcal P_2$ iff $|x - y| \le u^{-\gamma_1} v^{-\gamma_2}$. Small marks mean high degree: type-$i$ degrees have power-law tails $p_1((m,\infty)) \sim (\bar\gamma_2 m/2)^{-1/\gamma_1}$ and $p_2((m,\infty)) \sim (\bar\gamma_1 m/2)^{-1/\gamma_2}$, where $\bar\gamma_i = 1 - \gamma_i$. If $\gamma_1 + \gamma_2 < 1$ there is almost surely no infinite component; assume $(\gamma_1,\gamma_2) \in \mathcal S = \{\gamma_1 + \gamma_2 > 1\}$ and set $\Delta = \gamma_1 + \gamma_2 - 1$, $\Delta_i = (2\gamma_i - 1)\vee 0$.

**Epidemic.** Infected vertices recover at rate $1$; an infected type-1 vertex infects each neighbor at rate $\lambda_1 = \lambda$ and an infected type-2 vertex at rate $\lambda_2 = \lambda^a$, $a > 0$. Let $\theta(\lambda)$ be the annealed probability of survival forever from the root alone.

**Theorem.** Define the exponents of three strategies, star (S), bridge (B) and direct spreading (D),
$$\mu_{\mathsf S} = \frac{1+a}{\gamma_1}, \quad \mu_{\mathsf B} = \frac{1 + \bar\gamma_2 a}{\gamma_1\gamma_2}, \quad \mu_{\mathsf D} = \frac{\gamma_2 + \bar\gamma_2 a}{\Delta}, \qquad \nu_{\mathsf S} = \frac{1+a}{\gamma_2}, \quad \nu_{\mathsf B} = \frac{\bar\gamma_1 + a}{\gamma_1\gamma_2}, \quad \nu_{\mathsf D} = \frac{\bar\gamma_1 + \gamma_1 a}{\Delta},$$
$\mu_\star = \mu_{\mathsf S}\wedge\mu_{\mathsf B}\wedge\mu_{\mathsf D}$, $\nu_\star = \nu_{\mathsf S}\wedge\nu_{\mathsf B}\wedge\nu_{\mathsf D}$, and
$$A_\star = \mu_\star \wedge \big(1 + \bar\gamma_2\nu_\star\big) \wedge \big(1 + a - \Delta_2\nu_\star + \bar\gamma_1\mu_\star\big).$$
Then there is $C > 0$ such that for all small $\lambda$
$$\Big(\log\tfrac1\lambda\Big)^{-C}\lambda^{A_\star} \le \theta(\lambda) \le \Big(\log\tfrac1\lambda\Big)^{C}\lambda^{A_\star}.$$
In particular the critical value is $0$ throughout $\mathcal S$, and $A_\star$ is an explicit piecewise-rational function of $(\gamma_1,\gamma_2,a)$: for instance if $\gamma_2 \le \frac12$ then $(\mu_\star,\nu_\star) = (\mu_{\mathsf S}, \nu_{\mathsf B})$ for $a \le \bar\gamma_2/\Delta_2$ and $(\mu_{\mathsf S},\nu_{\mathsf S})$ otherwise, with analogous case splits when $\gamma_1 \le \frac12$ or both exceed $\frac12$.

## Expansion

A vertex of either type whose degree is much larger than $1/(\lambda_1\lambda_2) = \lambda^{-(1+a)}$ is a *star*: infection bounces between it and its neighbors for a long time. A type-1 vertex with mark $u$ has expected degree $u^{-\gamma_1}/\bar\gamma_2$, so reaching a star means reaching mark $\lambda^{\mu}$ with $\mu$ around $\mu_{\mathsf S}$. The three candidate strategies (root is itself a star; one step to a "bridge" vertex adjacent to stars; a direct chain of ever-lower marks) each cost a power of $\lambda$, and $A_\star$ is the cheapest, including the cost of the first one or two transmissions from the root. The upper bound sums over infection paths by length and number of distinct vertices, bounding each by the cheapest strategy compatible with its trace. Bipartiteness matters because consecutive transmissions alternate between rates $\lambda$ and $\lambda^a$ and between the two degree exponents.

## Sources

- John Fernley, Christian Hirsch and Daniel Valesin, "The contact process on a bipartite spatial network", arXiv:2604.00630 (2026), Section 1 (random connection hypergraph and contact process), Proposition 2, Theorem 3, Propositions 7, 8 and 31, <https://doi.org/10.48550/arXiv.2604.00630>.
