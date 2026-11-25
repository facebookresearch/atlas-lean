# The in-neighbours in the network digraph are the parents

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root $\rho$
and parent sets $\mathrm{pa}(v)$. For every node $v$, the nodes $u$ with an edge $u \to v$ in the
[digraph](g.md) $D_N$ of the network, with an edge $u \to v$ exactly when
$u \in \mathrm{pa}(v)$, form exactly the parent set: $\{u \in V : u \to v\} = \mathrm{pa}(v)$.
