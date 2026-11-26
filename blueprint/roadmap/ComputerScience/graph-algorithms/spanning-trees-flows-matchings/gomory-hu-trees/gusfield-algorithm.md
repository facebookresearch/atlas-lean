# Gusfield's algorithm: Gomory-Hu trees with n - 1 minimum cut computations

**Gusfield's algorithm.** Fix a root $r$ and let every vertex initially hang from $r$ (parent $p(v) = r$). Process the vertices $s \ne r$ once each in a fixed order: with $t = p(s)$, compute a minimum $s$-$t$ cut $X$ (with $s \in X$) and its value $\lambda$; re-hang below $s$ every other vertex $v$ with $p(v) = t$ and $v \in X$; if $p(t) \in X$, set $p(s) := p(t)$ and $p(t) := s$, swapping the recorded weights; record weight $\lambda$ on the edge $s\,p(s)$. For every symmetric submodular $f$ and every correct cut oracle, the final parent function is a weighted Gomory-Hu tree. Thus a Gomory-Hu tree of an $n$-vertex graph needs only $n - 1$ maximum-flow computations, all on the original graph, without contractions.

## Proof sketch

Invariant: for every processed $s$, the tree side of $s\,p(s)$ is a minimum $s$-$p(s)$ cut; uncrossing shows that later cuts can be assumed not to cross earlier ones, so re-hanging preserves the invariant.

## Depends on

- [Gomory-Hu trees](gomory-hu-tree.md)

## Proof depends on

- [Uncrossing minimum cuts of symmetric submodular functions](uncrossing-minimum-cuts.md)
- [Every symmetric submodular function has a Gomory-Hu tree](gomory-hu-existence.md)

## Sources

- D. Gusfield, "Very Simple Methods for All Pairs Network Flow Analysis", SIAM Journal on Computing 19(1), 1990.
- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
