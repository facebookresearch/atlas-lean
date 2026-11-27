# The tour from Prim's tree is a tour

For costs $d(u,v)$ on the vertices
$\{0, \dots, n-1\}$ with values in a linearly ordered type with a zero and commutative addition,
and any root $r$, the list returned by APPROX-TSP-TOUR with Prim's tree for $d$ and $r$ is a
permutation of $0, 1, \dots, n-1$: it visits every vertex exactly once.
