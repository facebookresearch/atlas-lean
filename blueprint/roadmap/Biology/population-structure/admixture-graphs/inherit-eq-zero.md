# Off the parent set the inheritance probability is zero

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. If
$u \notin \mathrm{pa}(v)$, then $\gamma(v, u) = 0$: a lineage only moves to a parent. This is the
phylogenetic-network instance of the corresponding property of an
[admixture graph](admixture-graph.md).
