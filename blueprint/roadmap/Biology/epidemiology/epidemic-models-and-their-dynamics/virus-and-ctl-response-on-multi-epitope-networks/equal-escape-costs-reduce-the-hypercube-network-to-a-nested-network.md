# Equal escape costs reduce the hypercube virus–CTL network to a nested network

**Binary-sequence model.** With $n$ epitopes, each viral variant is a binary string in $\{0,1\}^n$ (a $1$ at position $j$ means escape from the CTL response to epitope $j$), so there are up to $2^n$ variants on the hypercube graph $Q_n$, with edges between strings at Hamming distance $1$. Variant $i$ is attacked by the responses in its susceptible epitope set $\Lambda_i$ (the positions where it has a $0$). With $z_j = a_j Z_j$, $s_j = 1/\mathcal{I}_j$ and immunodominance $\mathcal{I}_j = a_j/\rho_j$,

$$
\dot x = 1 - x - x \sum_i \mathcal{R}_i y_i, \qquad \dot y_i = \gamma_i y_i \Big( \mathcal{R}_i x - 1 - \sum_{j \in \Lambda_i} z_j \Big), \qquad \dot z_j = \frac{\sigma_j}{s_j} z_j \Big( \sum_{i : j \in \Lambda_i} y_i - s_j \Big).
$$

This is the general virus–CTL network of [Lyapunov stability of saturated equilibria in virus–CTL networks](lyapunov-stability-of-saturated-equilibria-in-virus-ctl-networks.md) with $a_{ij} = a_j \mathbf{1}[j \in \Lambda_i]$.

**Cycles.** For $2 \le j \le n$ and $\ell = 2^j$, if variants $y_{k_1}, \dots, y_{k_\ell}$ form a simple $\ell$-cycle in $Q_n$ and $\sum_{i=1}^{\ell} (-1)^{d(y_{k_i}, y_w)} \mathcal{R}_{k_i} \ne 0$ ($y_w = 0\cdots0$ the wild type), there is no equilibrium at which all of them are positive. In particular, generically no four variants forming a square of $Q_n$ coexist at equilibrium.

**Theorem (uniform fitness costs).** Suppose each escape mutation multiplies fitness by the same factor $f \in (0,1)$, so $\mathcal{R}_i = f^{p}\mathcal{R}_1$ when $y_i$ has $p$ escape mutations, and the immunodominance hierarchy is strict, $s_1 < s_2 < \dots < s_n$. Index $y_1, \dots, y_{n+1}$ so that $\Lambda_i = \{i, \dots, n\}$ (variant $i$ has escaped exactly the $i - 1$ most dominant responses). Then every other variant $y_i$, $i \in [n+2, 2^n]$, goes extinct, and the dynamics follow the perfectly nested network: with

$$
\mathcal{Q}_0 = 1, \qquad \mathcal{Q}_k = \mathcal{Q}_{k-1} + (s_k - s_{k-1}) \mathcal{R}_k \quad (s_0 = 0),
$$

let $k$ be the largest index with $\mathcal{R}_k > \mathcal{Q}_k$ (or $k = 0$). Then $y_1, \dots, y_k$ and $z_1, \dots, z_k$ are uniformly persistent, $y_{k+1}$ also persists iff $\mathcal{R}_{k+1} > \mathcal{Q}_k$, and all other populations vanish.

So with equal costs, escape proceeds in order of immunodominance: the virus escapes the most dominant response first, and the persistent repertoire is a nested chain.

## Depends on

- [Lyapunov stability of saturated equilibria in virus–CTL networks](lyapunov-stability-of-saturated-equilibria-in-virus-ctl-networks.md)

## Expansion

The cycle obstruction comes from summing the equilibrium conditions $\mathcal{R}_{k_i} x^* - 1 - \sum_{j \in \Lambda_{k_i}} z_j^* = 0$ with alternating signs around the cycle: along a cycle of $Q_n$ each epitope is gained and lost equally often, so the $z_j^*$ terms cancel and one is left with $x^* \sum_i (-1)^i \mathcal{R}_{k_i} = 0$. For uniform costs the proof applies the saturation theorem to the equilibrium of the nested subnetwork $y_1, \dots, y_{n+1}$ and checks the invasion rate of every off-path variant $y_\ell$ with $p$ escapes: if $p > k$ its rate is at most $f^p\mathcal{R}_1/\mathcal{Q}_k - 1 < f^k \mathcal{R}_1/\mathcal{Q}_k - 1 \le 0$; if $p \le k$ it is still targeted by some persistent response among $z_1, \dots, z_k$, and since the equilibrium responses decrease along the hierarchy ($\bar z_i - \bar z_{i-1} = -f^{i-2}\mathcal{R}_1 (f-1)^2/\mathcal{Q}_k < 0$), its rate is negative as well.

## Sources

- C. J. Browne, H. L. Smith, "Dynamics of Virus and Immune Response in Multi-Epitope Network", arXiv:1705.01188 (2017): binary-sequence hypercube model, immunodominance $\mathcal{I}_j$, Proposition on cycles in the hypercube, Theorem 2 (nested network, with the recursion for $\mathcal{Q}_k$), Section on uniform fitness costs for escape on the full $n$-epitope network (Theorem 6 and its proof). <https://doi.org/10.48550/arXiv.1705.01188> Published version: Journal of Mathematical Biology 77 (2018) 1833–1870, <https://doi.org/10.1007/s00285-018-1224-z>.
