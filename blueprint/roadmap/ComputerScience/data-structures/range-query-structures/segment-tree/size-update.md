# Point update preserves the size of a segment tree

For every segment tree $t$ over an
additive monoid, every index $i$ and every value $y$, the point update of $t$ at $i$ with $y$
has the same size as $t$.

Every node on the update path keeps its cached segment length.
