# Blocking at a node is independent of path direction

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ and $Z$ a set of nodes. For nodes
$u, m, w$, the consecutive nodes $u, m, w$ are [blocked](blocked-at.md) by $Z$ if and only if
$w, m, u$ are blocked by $Z$: blocking at a node does not depend on the direction in which the
path is read.
