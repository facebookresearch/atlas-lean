# Inheritance probabilities are at most one

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$.
Then $\gamma(v, u) \le 1$ for all nodes $v$ and $u$; with [nonnegativity](inherit-nonneg.md),
$\gamma(v, u) \in [0, 1]$. This is the phylogenetic-network instance, a special case, of the
[bound on the admixture proportions](prop-le-one.md) of admixture graphs.
