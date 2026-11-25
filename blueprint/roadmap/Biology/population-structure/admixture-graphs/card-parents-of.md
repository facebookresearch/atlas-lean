# Off the root a node has one or two parents in the network digraph

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root $\rho$
and parent sets $\mathrm{pa}(v)$. Every node $v \ne \rho$ has one or two in-neighbours in the
[digraph](g.md) $D_N$ of the network, with an edge $u \to v$ exactly when
$u \in \mathrm{pa}(v)$: the set $\{u \in V : u \to v\}$ has one element (a tree node) or two (a
reticulation node).
