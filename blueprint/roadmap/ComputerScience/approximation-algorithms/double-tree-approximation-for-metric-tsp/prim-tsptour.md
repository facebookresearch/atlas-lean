# APPROX-TSP-TOUR with Prim's tree

Given costs $d(u,v)$ on the vertices
$\{0, \dots, n-1\}$ with values in a linearly ordered type with a zero and commutative addition,
and a root $r$, the tour is $r$ followed by the vertices of the forest of Prim's tree below $r$
in preorder. Its running time counts one unit per vertex of the tour; running Prim's algorithm
and building the forest are not counted.

This is CLRS APPROX-TSP-TOUR, with the minimum spanning tree computed by Prim.
