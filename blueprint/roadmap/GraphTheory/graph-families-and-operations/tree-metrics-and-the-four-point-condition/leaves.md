# Leaves of a rooted binary tree with root distances

The leaves of a [rooted binary tree](rtree.md) form the list of triples (label, distance to the root, number of edges to the root): $[(x, 0, 0)]$ for a leaf $x$; for an internal vertex with children $l, r$ on edges of lengths $a, b$, the leaves of $l$ with distances increased by $a$ and edge counts by $1$, followed by those of $r$ with distances increased by $b$ and edge counts by $1$.
