# Descendants come later in the topological order

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$, listed in a topological order. If
$j$ is a descendant of $i$ in the graph of $B$ (reachable from $i$ along arrows; every node is
its own descendant), then $i \le j$.
