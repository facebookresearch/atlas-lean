# Digraph of a phylogenetic network

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root $\rho$
and parent sets $\mathrm{pa}(v)$. The digraph $D_N$ of the network has vertex set $V$ and an edge
$u \to v$ exactly when $u \in \mathrm{pa}(v)$: edges run from ancestor to descendant, from each
parent to its child.
