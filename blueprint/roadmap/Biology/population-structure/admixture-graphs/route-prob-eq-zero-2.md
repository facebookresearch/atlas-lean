# In a network, sending a lineage to a non-parent has probability zero

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. Let
$v$ be a node, the root included, and let $a = (a_0, \dots, a_{k - 1}) \in V^k$ be an assignment of
$k$ lineages to nodes. If some lineage $i$ is sent to a node $a_i \notin \mathrm{pa}(v)$, then the
[routing probability](route-prob-2.md) $R(v, a) = \prod_{i < k} \gamma(v, a_i)$ is $0$. This is the
phylogenetic-network instance, a special case, of the [corresponding result](route-prob-eq-zero.md)
of admixture graphs.
