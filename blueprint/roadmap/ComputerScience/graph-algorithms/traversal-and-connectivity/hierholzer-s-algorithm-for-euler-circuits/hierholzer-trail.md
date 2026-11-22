# Hierholzer's algorithm returns a trail in a directed multigraph

Let $G$ be a directed
adjacency graph, read as a multigraph with one edge per adjacency entry, and let $s$ and $t$ be
vertices such that $G$ is semi-balanced for $s$ and $t$. Then the vertex sequence $W$ returned by
Hierholzer's algorithm on $G$ from $s$ starts at $s$ and ends at $t$, and the edge list of $G$ is a
permutation of the list of consecutive pairs of $W$ followed by some further list of pairs. So $W$
is a walk from $s$ to $t$ that uses each edge occurrence at most once; reachability is not
assumed.
