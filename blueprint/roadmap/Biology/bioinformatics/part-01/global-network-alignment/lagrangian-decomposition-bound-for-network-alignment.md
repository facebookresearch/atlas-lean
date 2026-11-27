# Lagrangian decomposition bound for network alignment

**Setting.** Network alignment of $G_1 = (V_1,E_1)$ and $G_2 = (V_2,E_2)$ with node scores $\sigma \ge 0$ and symmetric pair scores $\tau \ge 0$ is the maximum structural matching problem on the complete bipartite alignment graph, each unordered pair of distinct alignment edges counted once. Split each structural variable into two directed copies $\vec y_{ijkl}$ and $\vec y_{klij}$, one for each ordered pair of distinct alignment edges, with weights $\vec\tau(i,j,k,l) = \vec\tau(k,l,i,j) = \tau(i,j,k,l)/2$, so that $\vec\tau(i,j,k,l) + \vec\tau(k,l,i,j) = \tau(i,j,k,l)$. Write $\delta(v)$ for the alignment edges at a vertex $v \in V_1 \cup V_2$. The split program is

$$\max \sum_{(i,j)} \sigma(i,j)\,x_{ij} + \sum_{(i,j)}\ \sum_{(k,l) \neq (i,j)} \vec\tau(i,j,k,l)\,\vec y_{ijkl}$$

subject to

- $\sum_{(i,j)\in\delta(v)} x_{ij} \le 1$ for every vertex $v$;
- $\vec y_{ijkl} \le x_{ij}$, and the partner degree constraints $\sum_{(k,l)\in\delta(v),\,(k,l) \neq (i,j)} \vec y_{ijkl} \le x_{ij}$ for every alignment edge $(i,j)$ and every vertex $v$;
- the coupling constraints $\vec y_{ijkl} = \vec y_{klij}$;
- all variables binary.

The partner degree constraints are valid for the original problem: when $\vec y_{ijkl} = x_{ij}x_{kl}$ and $x$ is a matching, at most one partner $(k,l)$ meets each vertex $v$.

**Theorem.**
1. The optimal value of the split program is the maximum structural score. Every feasible point has objective at most the structural score of the matching with characteristic vector $x$, with equality when $\vec y_{ijkl} = x_{ij}x_{kl}$ for all ordered pairs.
2. Relaxing the coupling constraints with multipliers satisfying $\lambda_{ijkl} = -\lambda_{klij}$ gives the relaxed problem

$$L(\lambda) = \max \sum_{(i,j)} \sigma(i,j)\,x_{ij} + \sum_{(i,j)}\ \sum_{(k,l) \neq (i,j)} \big(\vec\tau(i,j,k,l) + \lambda_{ijkl}\big)\,\vec y_{ijkl}$$

over the remaining constraints, including the partner degree constraints. For every $\lambda$, $L(\lambda)$ is an upper bound on the optimal alignment score.
3. $L(\lambda)$ can be computed in polynomial time by bipartite matchings. For each alignment edge $(i,j)$, let $p_{ij} = \sigma(i,j) + m_{ij}$, where $m_{ij}$ is the value of a maximum-weight bipartite matching on the alignment edges $(k,l) \neq (i,j)$ with weights $\vec\tau(i,j,k,l) + \lambda_{ijkl}$, using only positive weights. Then $L(\lambda)$ is the value of a maximum-weight bipartite matching with weights $p_{ij}$, using only positive weights.

Without the partner degree constraints, the relaxed program is a different and weaker bound: once the coupling equalities are dropped, $x_{ij} = 1$ allows every partner with positive coefficient, including two partners that share a vertex, so its value is $\sigma(i,j)$ plus the sum of all positive coefficients $\vec\tau(i,j,k,l) + \lambda_{ijkl}$, which can strictly exceed $p_{ij}$.

## Depends on

- [Maximum structural matching formulation of network alignment](maximum-structural-matching-formulation-of-network-alignment.md)

## Proof depends on

- [Weak duality](../../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-le-primal-value.md)

## Expansion

Each directed variable $\vec y_{ijkl}$ is bound to a single alignment variable $x_{ij}$ by $\vec y_{ijkl} \le x_{ij}$ and by the partner degree constraints of $(i,j)$, so once the coupling equalities are dropped the problem decomposes: if $x_{ij} = 0$ its directed variables vanish, and if $x_{ij} = 1$ its directed variables range over the matchings of the alignment graph minus $(i,j)$, the best of which has value $m_{ij}$. The outer choice of $x$ is then a matching with profits $p_{ij}$. The bound follows from weak Lagrangian duality, since the antisymmetry of $\lambda$ makes the penalty term vanish on any point satisfying the coupling. Subgradient optimization over $\lambda$ tightens the upper bound, and the structural completion of each relaxed matching (adding all structural matches between its chosen edges) gives a feasible lower bound, so the gap certifies optimality when it closes. Klau's displayed relaxed problem (17)–(22) omits the partner degree constraints while the proof of Theorem 3 evaluates it with inner matchings; the statement above keeps the constraints so that the two agree.

## Sources

- G. W. Klau, "A new graph-based method for pairwise global network alignment", BMC Bioinformatics 10(Suppl 1):S59 (2009), ILP (11)–(16), Theorem 2, relaxed problem (17)–(22) and Theorem 3 (with the partner degree constraints added here), <https://doi.org/10.1186/1471-2105-10-S1-S59>, PMCID PMC2648773.
