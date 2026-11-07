# The approximate TSP tour is a tour

Let $V$ be a list of distinct vertices, and let $r$
and $F$ be such that $r$ followed by the vertices of the forest $F$ in preorder is a permutation
of $V$ (the tree with root $r$ and subtree forest $F$ spans $V$). Then the list returned by
`APPROX-TSP-TOUR` on $r$ and $F$ is a tour of $V$: it is a permutation of $V$.
