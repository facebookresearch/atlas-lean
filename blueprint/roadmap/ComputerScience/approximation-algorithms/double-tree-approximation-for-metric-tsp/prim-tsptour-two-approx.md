# APPROX-TSP-TOUR with Prim's tree is a 2-approximation

Let $d$ be a real metric cost
on the vertices $\{0, \dots, n-1\}$ (symmetric, zero on the diagonal, nonnegative, and
satisfying the triangle inequality), and let $r$ be a vertex. Then the cost of the closed tour
through the list returned by APPROX-TSP-TOUR with Prim's tree for $d$ and $r$ is at most twice
the cost of the closed tour through $H$, for every list $H$ that visits each of
$0, 1, \dots, n-1$ exactly once.

This is CLRS Theorem 35.2, with the minimum spanning tree computed by Prim.
