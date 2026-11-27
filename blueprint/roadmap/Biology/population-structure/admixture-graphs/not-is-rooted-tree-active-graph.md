# A reticulation with 0 < γ < 1 means the active graph is not a tree

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. If
a node $v$ has exactly the two parents $u_1 \ne u_2$, $\mathrm{pa}(v) = \{u_1, u_2\}$, and
$0 < \gamma(v, u_1) < 1$, then both edges into $v$ are used with positive probability, so the
[active graph](active-graph.md) is not a rooted tree with root $\rho$: such a tree has exactly one
edge into every node other than $\rho$.
