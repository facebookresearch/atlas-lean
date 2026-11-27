# Forest of Prim's tree

Given costs $d(u,v)$ on the vertices $\{0, \dots, n-1\}$ with
values in a linearly ordered type with a zero and commutative addition, and a root $r$, take
Prim's parent array for $d$ and $r$ (Prim's algorithm run from $r$ on the complete graph with
edge weights $d(u,v) + d(v,u)$). This forest is the forest of the subtrees below $r$ in that
parent array, cut off $n$ levels below $r$, in left-child right-sibling form, with the children
of each vertex in vertex order.
