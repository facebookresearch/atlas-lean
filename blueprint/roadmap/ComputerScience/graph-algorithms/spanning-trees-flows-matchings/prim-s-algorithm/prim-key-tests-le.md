# Bound on key comparisons in Prim's algorithm

Let $W$ be a linearly ordered type with a
zero element, let $D$ be a directed adjacency structure on the vertices $0, \dots, n-1$ with
adjacency lists $A(u)$, let $w$ assign a weight in $W$ to every unordered pair of vertices, not
necessarily distinct, and let $r$ be a vertex. The number of inspected adjacency entries that
Prim's algorithm on $D$, $w$ and $r$ finds still in the queue, which is its number of key
comparisons, is at most the sum of the lengths $|A(u)|$ over all vertices $u$.
