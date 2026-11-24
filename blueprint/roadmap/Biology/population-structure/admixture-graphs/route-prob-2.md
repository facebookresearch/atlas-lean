# Routing kernel of a phylogenetic network

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. For
a node $v$, a natural number $k$ and an assignment $a = (a_0, \dots, a_{k - 1}) \in V^k$ of $k$
lineages to nodes, the routing probability is

$$R(v, a) = \prod_{i < k} \gamma(v, a_i).$$

At a node $v \ne \rho$ it describes $k$ lineages entering $v$, traced backward in time, that move to
parents independently, lineage $i$ to $a_i$, and these values form a probability distribution on
$V^k$ ([rows sum to one](sum-route-prob-2.md)). At the root, which has no parent, every assignment
of $k > 0$ lineages has value $0$ ([root row](route-prob-root-2.md)). For $k = 0$ the product is
empty and the single empty assignment has probability $1$, at every node. It is the
[routing kernel](route-prob.md) of the underlying admixture graph.
