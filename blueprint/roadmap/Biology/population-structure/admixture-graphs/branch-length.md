# Branch length as an age difference

Let $N$ be a [phylogenetic network](phylo-network.md) on a finite set $V$ of nodes, with root
$\rho$, parent sets $\mathrm{pa}(v)$ and node ages $t(v)$. For nodes $u$ and $v$, the branch length
is the age difference $\ell(u, v) = t(u) - t(v)$. It is defined for every pair of nodes; for an edge
from a parent $u$ to its child $v$ it is the length of that branch, and it is then
[nonnegative](nonneg-lengths-2.md).
