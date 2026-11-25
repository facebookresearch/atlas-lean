# With zero-one inheritance probabilities routing is deterministic

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$, and
let $\gamma(v, u) \in \{0, 1\}$ for all nodes $v$ and $u$. Then every node $v \ne \rho$ has a parent
$u \in \mathrm{pa}(v)$ such that for every natural number $k$ and every assignment
$a = (a_0, \dots, a_{k - 1}) \in V^k$ of $k$ lineages to nodes, the
[routing probability](route-prob-2.md) $R(v, a) = \prod_{i < k} \gamma(v, a_i)$ is $1$ if $a_i = u$
for every $i$ and $0$ otherwise: every lineage moves to the parent $u$, the one with
$\gamma(v, u) = 1$.
