# Hierholzer's algorithm finds Euler circuits in directed multigraphs

Let $G$ be a directed
adjacency graph, read as a multigraph with one edge per adjacency entry, that is balanced (every
vertex is the source of exactly as many edge occurrences as it is the target of), and let $s$ be a
vertex such that the source of every edge of $G$ is reachable from $s$. Then the vertex sequence
returned by Hierholzer's algorithm on $G$ from $s$ is an Euler circuit of $G$ from $s$.

## Sources

- CLRS, third edition, Problem 22-3, sufficiency with the algorithm; strong connectivity is weakened to reachability from $s$ of the source of every edge.
