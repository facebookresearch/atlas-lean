# Kruskal's algorithm returns a maximal forest

Let $G$ be a simple graph on a finite vertex
set and let $L$ be a list of unordered pairs of vertices such that a pair is an edge of $G$ if and
only if it occurs in $L$. Then the matroid greedy algorithm run with the forest oracle of $G$ on
$L$ returns a base of the graphic matroid of $G$, that is, a maximal forest of $G$.
