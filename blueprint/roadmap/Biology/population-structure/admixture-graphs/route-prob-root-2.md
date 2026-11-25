# At the network root every nonempty routing has probability zero

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and [inheritance probabilities](inherit.md) $\gamma(v, u)$. For
every natural number $k > 0$ and every assignment $a = (a_0, \dots, a_{k - 1}) \in V^k$ of $k$
lineages to nodes, the [routing probability](route-prob-2.md)
$R(v, a) = \prod_{i < k} \gamma(v, a_i)$ at the root is $R(\rho, a) = 0$: the root has no parent.
For $k = 0$ the empty assignment has probability $1$. This is the phylogenetic-network instance, a
special case, of the [corresponding result](route-prob-root.md) of admixture graphs.
