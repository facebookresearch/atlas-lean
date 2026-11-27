# Total biomass bound in homogeneous flow stream networks

**Leveled graph.** A directed graph $G$ with node set $V$ and a level function $f : V \to \mathbb{Z}_{\ge 0}$ is *leveled* if every level $0 \le k \le \max_i f(i)$ is attained and there is no edge between nodes $i, j$ with $|f(i) - f(j)| \ne 1$. Larger levels are further downstream.

**Homogeneous flow stream network.** $(G, f, L)$ is a homogeneous flow stream network if the connection matrix $L$ is irreducible, every edge $i \to j$ has a reverse edge $j \to i$, and the movement weight on an edge is $\ell_{ji} = d + q$ when it goes one level downstream and $d$ when it goes one level upstream, with constants $d, q > 0$ (random movement $d$, drift $q$). Write $L = dD + qQ$, with diagonal entries $\ell_{ii} = -\sum_{j \ne i} \ell_{ji}$.

**Single-species model.** With growth rates $\mathbf r = (r_1, \dots, r_n) > \mathbf 0$ and a common carrying capacity $k > 0$,

$$\frac{du_i}{dt} = \sum_{j=1}^n (dD_{ij} + qQ_{ij})\,u_j + r_i u_i\Big(1 - \frac{u_i}{k}\Big), \qquad i = 1, \dots, n .$$

Because $L$ is irreducible and essentially nonnegative, this model has a unique positive equilibrium $\mathbf u^*$, which is globally asymptotically stable. Its total biomass is $\mathcal K = \sum_i u_i^*$.

**Lemma (null vector).** The positive solution of $L\mathbf v = 0$ is, up to a constant multiple, $v_i = \big((d+q)/d\big)^{f(i)}$.

**Theorem (biomass upper bound).** If $\sum_i r_i = r > 0$, then

$$\mathcal K \le k \sum_{i=1}^n \Big(1 + \frac{q}{d}\Big)^{f(i)} .$$

The bound is attained when $r_i = 0$ at every node with positive level, i.e. when all resources sit at the upstream ends ($f(i) = 0$). In that case $u_i^* = k\big((d+q)/d\big)^{f(i)}$.

## Expansion

At equilibrium, summing the equations kills the movement term (columns of $L$ sum to zero), so $\sum_i r_i u_i^*(1 - u_i^*/k) = 0$. When the only growing nodes sit at level $0$, the remaining nodes carry no growth term, and their equations force $\mathbf u^*$ to be proportional to the null vector $\mathbf v$ on the downstream part. The growing nodes must then sit exactly at carrying capacity, which gives $u_i^* = k v_i$ with $v_i = (1 + q/d)^{f(i)}$. Drift piles biomass up downstream by the factor $(1 + q/d)$ per level. With resources placed elsewhere, a sign-pattern argument on net flows between adjacent levels shows that no equilibrium can exceed this profile.

## Sources

- Tung D. Nguyen, Yixiang Wu, Tingting Tang, Amy Veprauskas, Ying Zhou, Behzad Djafari Rouhani and Zhisheng Shuai, "Impact of resource distributions on the competition of species in stream environment", Journal of Mathematical Biology 87 (2023), 62, <https://doi.org/10.1007/s00285-023-01978-6>; numbering as in arXiv:2306.05555: Lemma 2.1, Definitions 4.1 and 4.2, Lemma 4.3, Theorem 4.4.
