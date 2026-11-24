# d-separation

**d-separation** (Pearl 1988; Pearl 2009, Definition 1.2.3): let $B$ be a Bayesian network on the
nodes $0, \dots, n - 1$ and $X, Y, Z$ sets of nodes. Then $Z$ d-separates $X$ from $Y$ if every
path in the skeleton between a node of $X$ and a node of $Y$ is [blocked](path-blocked.md) by
$Z$. In particular this requires $X$ and $Y$ to be disjoint, since a one-node path cannot be
blocked.
