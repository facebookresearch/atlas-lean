# Parents separate a node from its other non-descendants

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$. In the graph of $B$, the set of
parents of a node $k$ d-separates $\{k\}$ from the set of nodes that are neither descendants
nor parents of $k$: a path leaving $k$ through a parent is blocked at that parent, and a path
leaving $k$ through a child must turn back at a collider that is a descendant of $k$, hence not
a parent.
