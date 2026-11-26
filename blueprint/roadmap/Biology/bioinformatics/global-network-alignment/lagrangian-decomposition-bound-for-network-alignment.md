# Lagrangian decomposition bound for network alignment

**Setting.** Network alignment of $G_1 = (V_1,E_1)$ and $G_2 = (V_2,E_2)$ with node scores $\sigma \ge 0$ and pair scores $\tau \ge 0$ is the maximum structural matching problem on the complete bipartite alignment graph. Split each structural variable into two directed copies $\vec y_{ijkl}$ and $\vec y_{klij}$ with weights $\vec\tau(i,j,k,l) = \vec\tau(k,l,i,j) = \tau(i,j,k,l)/2$, so that $\vec\tau(i,j,k,l) + \vec\tau(k,l,i,j) = \tau(i,j,k,l)$. The split program is

$$\max \sum_{(i,j)} \sigma(i,j)\,x_{ij} + \sum_{(i,j)}\sum_{(k,l)} \vec\tau(i,j,k,l)\,\vec y_{ijkl}$$

subject to $\sum_{(i,j)\in\delta(v)} x_{ij} \le 1$ for every vertex $v$, $\vec y_{ijkl} \le x_{ij}$, $\vec y_{ijkl} = \vec y_{klij}$, and all variables binary.

**Theorem.**
1. Feasible solutions of the split program are exactly the structural matchings of the alignment graph, with objective value equal to the structural score.
2. Relaxing the coupling constraints $\vec y_{ijkl} = \vec y_{klij}$ with multipliers satisfying $\lambda_{ijkl} = -\lambda_{klij}$ gives the relaxed problem

$$L(\lambda) = \max \sum_{(i,j)} \sigma(i,j)\,x_{ij} + \sum_{(i,j)}\sum_{(k,l)} \big(\vec\tau(i,j,k,l) + \lambda_{ijkl}\big)\,\vec y_{ijkl}$$

over the remaining constraints. For every $\lambda$, $L(\lambda)$ is an upper bound on the optimal alignment score.
3. $L(\lambda)$ can be computed in polynomial time by bipartite matchings: for each alignment edge $(i,j)$, its profit $p_{ij} = \sigma(i,j) + $ (the value of a maximum-weight bipartite matching on the edges $(k,l)$ with weights $\vec\tau(i,j,k,l) + \lambda_{ijkl}$, restricted to positive weights) is computed, and then a maximum-weight bipartite matching with weights $p_{ij}$ gives $L(\lambda)$.

## Depends on

- [Maximum structural matching formulation of network alignment](maximum-structural-matching-formulation-of-network-alignment.md)

## Expansion

Each directed variable $\vec y_{ijkl}$ is bound to a single alignment variable $x_{ij}$ by $\vec y_{ijkl} \le x_{ij}$, so once the coupling equalities are dropped the problem decomposes: if $x_{ij} = 0$ its directed variables vanish, and if $x_{ij} = 1$ the best choice of partners $(k,l)$ is itself a matching problem. The bound follows from weak Lagrangian duality, and the antisymmetry of $\lambda$ means the penalty term vanishes on any solution satisfying the coupling. Subgradient optimization over $\lambda$ tightens the upper bound, and the structural completion of each relaxed matching (adding all structural matches between its chosen edges) gives a feasible lower bound, so the gap certifies optimality when it closes.

## Sources

- G. W. Klau, "A new graph-based method for pairwise global network alignment", BMC Bioinformatics 10(Suppl 1):S59 (2009), ILP (11)–(16), Theorem 2, relaxed problem (17)–(22) and Theorem 3, <https://doi.org/10.1186/1471-2105-10-S1-S59>, PMCID PMC2648773.
