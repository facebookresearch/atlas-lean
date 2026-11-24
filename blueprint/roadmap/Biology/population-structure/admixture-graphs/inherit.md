# Inheritance probability of a parent

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and node ages. For nodes $v$ and $u$, the inheritance
probability $\gamma(v, u)$ is the admixture proportion of $u$ in $v$ in the underlying
[admixture graph](admixture-graph.md): the probability that a lineage at $v$ traces back to the
parent $u$. It is [nonnegative](inherit-nonneg.md),
[$0$ unless $u \in \mathrm{pa}(v)$](inherit-eq-zero.md) and, at every node $v \ne \rho$,
[sums to $1$](sum-inherit.md) over the parents of $v$.
