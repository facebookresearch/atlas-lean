# Blocking at a node of a path

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ and $Z$ a set of nodes. Consecutive
nodes $u, m, w$ of a path are blocked by $Z$ (Pearl 2009, Definition 1.2.3) if either $m$ is a
collider $u \to m \leftarrow w$ none of whose descendants is in $Z$, or $m$ is not a collider (a
chain or a fork) and $m \in Z$.
