# Off the root the inheritance probabilities sum to one

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. For
every node $v \ne \rho$,

$$\sum_{u \in \mathrm{pa}(v)} \gamma(v, u) = 1.$$

At the root the parent set is empty and the sum is $0$. This is the phylogenetic-network instance of
the normalization of the proportions of an [admixture graph](admixture-graph.md).
