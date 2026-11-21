# The path used by one Edmonds–Karp step

For a flow $f$, the path used by one step of the algorithm is the shortest residual path from $s$ to $t$ returned by the breadth-first search of [step](step.md), or the empty list when $t$ is not reachable. It is the augmenting path $P^k$ of Edmonds and Karp.
