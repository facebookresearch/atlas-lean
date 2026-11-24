# Network routing kernel rows at non-root nodes sum to one

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. For
every node $v \ne \rho$ and every natural number $k$, the routing probabilities of all assignments
of $k$ lineages to nodes sum to one:

$$\sum_{a \in V^k} R(v, a) = 1,$$

with $R(v, a) = \prod_{i < k} \gamma(v, a_i)$ the [routing probability](route-prob-2.md): at every
non-root node the routing probabilities form a probability distribution on $V^k$. This is the
phylogenetic-network instance, a special case, of the
[row sums of the routing kernel](sum-route-prob.md) of admixture graphs.
