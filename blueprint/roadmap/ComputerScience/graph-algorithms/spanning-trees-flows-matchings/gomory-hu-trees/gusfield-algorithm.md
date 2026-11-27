# Gusfield's algorithm: Gomory-Hu trees with n - 1 minimum cut computations

**Gusfield's algorithm.** Fix a root $r$ and let every vertex hang from $r$ (parent $p(v) = r$, with $p(r) = r$); each vertex $v \ne r$ carries a weight $\ell(v)$ for the edge $v\,p(v)$. Process the vertices $s \ne r$ once each in a fixed order: with $t = p(s)$, compute a minimum $s$-$t$ cut $X$ (with $s \in X$) and its value $\lambda$, and set $\ell(s) := \lambda$; re-hang below $s$ every other vertex $v$ with $p(v) = t$ and $v \in X$; then, if $p(t) \in X$, set $p(s) := p(t)$, $p(t) := s$, $\ell(s) := \ell(t)$ and $\ell(t) := \lambda$. For every real-valued symmetric submodular $f$ and every correct cut oracle, the final parent function with the weights $\ell$ is a weighted Gomory-Hu tree. Thus a Gomory-Hu tree of an $n$-vertex graph needs only $n - 1$ maximum-flow computations, all on the original graph, without contractions (Williamson, Algorithm 3.8, Theorem 3.37 and p. 91, with the roles of $s$ and $t$ exchanged and $X$ replaced by its complement).

## Proof sketch

Invariant: for every processed $s$, the tree side of $s\,p(s)$ is a minimum $s$-$p(s)$ cut; uncrossing shows that later cuts can be assumed not to cross earlier ones, so re-hanging preserves the invariant. The swap moves each weight with its edge: afterwards the edge $s\,p(s)$ is the old edge $t\,p(t)$ and keeps $\ell(t)$, and the new edge $t\,s$ carries $\lambda$, the value of the cut just computed between $s$ and $t$. Writing $\lambda$ on $s\,p(s)$ after the swap would put it on the wrong edge: with root $1$, order $2, 3$ and edge weights $w(12) = 1$, $w(13) = 2$, $w(23) = 3$, the second step would give the edge $3\,1$ weight $4$ instead of $\lambda(1, 3) = 3$.

## Depends on

- [Gomory-Hu trees](gomory-hu-tree.md)

## Proof depends on

- [Uncrossing minimum cuts of symmetric submodular functions](uncrossing-minimum-cuts.md)
- [Every symmetric submodular function has a Gomory-Hu tree](gomory-hu-existence.md)

## Sources

- D. P. Williamson, "Network Flow Algorithms", Cambridge University Press, 2019, Section 3.4: Theorem 3.37 (p. 90), Algorithm 3.8 and the extension to symmetric submodular functions (p. 91), chapter notes (p. 95); author-posted edition: <https://www.networkflowalgs.com/book.pdf>.
- D. Gusfield, "Very Simple Methods for All Pairs Network Flow Analysis", SIAM Journal on Computing 19(1), 1990.
- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
