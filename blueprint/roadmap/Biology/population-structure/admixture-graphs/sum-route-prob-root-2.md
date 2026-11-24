# With at least one lineage, the network root row has mass zero

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. For
every natural number $k > 0$, the routing probabilities at the root sum to zero over all assignments
of $k$ lineages to nodes:

$$\sum_{a \in V^k} R(\rho, a) = 0,$$

with $R(v, a) = \prod_{i < k} \gamma(v, a_i)$ the [routing probability](route-prob-2.md); so for
$k > 0$ the root row is not a probability distribution. This is the phylogenetic-network instance, a
special case, of the [root row of the routing kernel](sum-route-prob-root.md) of admixture graphs.
