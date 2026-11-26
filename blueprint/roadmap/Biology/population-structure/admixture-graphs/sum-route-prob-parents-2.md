# Off the root, network routing over parent assignments sums to one

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. For
every node $v \ne \rho$ and every natural number $k$, the routing probabilities of the assignments
of the $k$ lineages to parents of $v$ sum to one:

$$\sum_{a \in \mathrm{pa}(v)^k} R(v, a) = 1,$$

with $R(v, a) = \prod_{i < k} \gamma(v, a_i)$ the [routing probability](route-prob-2.md). This is
the phylogenetic-network instance, a special case, of the
[normalization over parent assignments](sum-route-prob-parents.md) of admixture graphs.
