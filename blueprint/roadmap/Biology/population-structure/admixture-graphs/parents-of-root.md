# The root has no parent in the network digraph

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root $\rho$
and parent sets $\mathrm{pa}(v)$. The root has no in-neighbour in the [digraph](g.md) $D_N$
of the network, with an edge $u \to v$ exactly when $u \in \mathrm{pa}(v)$:
$\{u \in V : u \to \rho\} = \varnothing$.
