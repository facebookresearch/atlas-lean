# With zero-one inheritance probabilities the active graph is a tree

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. If
$\gamma(v, u) \in \{0, 1\}$ for all nodes $v$ and $u$, then the [active graph](active-graph.md), the
edges $u \to v$ with $u \in \mathrm{pa}(v)$ and $\gamma(v, u) > 0$, is a rooted tree with root
$\rho$: it is acyclic, has no edge into $\rho$, every node $v \ne \rho$ has exactly one node $u$
with an edge $u \to v$, and every node is reachable from $\rho$ along its edges.
