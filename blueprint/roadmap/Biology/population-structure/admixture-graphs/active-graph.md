# Active graph of a phylogenetic network

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. The
active graph of $N$ has vertex set $V$ and an edge $u \to v$ exactly when $u \in \mathrm{pa}(v)$ and
$\gamma(v, u) > 0$: the edges a lineage uses with positive probability.
