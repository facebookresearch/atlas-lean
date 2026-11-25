# Parent-to-child digraph of a phylogenetic network

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root $\rho$
and parent sets $\mathrm{pa}(v)$. The parent-to-child digraph $D_N$ of $N$ has vertex set $V$ and an
edge $u \to v$ exactly when $u$ is a parent of $v$, $u \in \mathrm{pa}(v)$.

This is the digraph of the network: its edges run from ancestor to descendant, from each parent to
its child.
