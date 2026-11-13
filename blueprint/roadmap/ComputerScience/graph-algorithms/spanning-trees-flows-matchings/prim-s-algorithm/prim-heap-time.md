# Logarithmic heap cost of Prim's algorithm

Let $W$ be a linearly ordered type with a zero
element, let $D$ be a directed adjacency structure on the vertices $0, \dots, n-1$ with adjacency
lists $A(u)$, let $w$ assign a weight in $W$ to every unordered pair of vertices, not necessarily
distinct, let $r$ be a vertex, and let $a$ be the sum of the lengths $|A(u)|$ over all vertices
$u$. Each of the five heap event counts of Prim's algorithm on $D$, $w$ and $r$ (comparisons,
swaps, reads of the position vector, writes to the position vector, and entry appends, pops or
replacements) is at most $20(2n + a)(\lfloor \log_2(n + 1) \rfloor + 1) + a$.
