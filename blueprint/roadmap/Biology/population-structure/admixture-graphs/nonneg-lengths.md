# Property that all branch lengths are nonnegative

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and node ages $t(v)$. The network has nonnegative branch
lengths when $\ell(u, v) = t(u) - t(v) \ge 0$ for every edge $u \to v$ of the
[digraph](g.md) $D_N$ of the network, with an edge $u \to v$ exactly when
$u \in \mathrm{pa}(v)$.
