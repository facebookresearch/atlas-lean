# Routing probabilities of a phylogenetic network are nonnegative

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. For
every node $v$, the root included, every natural number $k$ and every assignment
$a = (a_0, \dots, a_{k - 1}) \in V^k$ of $k$ lineages to nodes, the
[routing probability](route-prob-2.md) $R(v, a) = \prod_{i < k} \gamma(v, a_i)$ is nonnegative. This
is the phylogenetic-network instance, a special case, of the
[nonnegativity of routing probabilities](route-prob-nonneg.md) of admixture graphs.
