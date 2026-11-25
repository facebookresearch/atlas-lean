# Euler circuit criterion for directed multigraphs

Let $G$ be a directed adjacency graph,
read as a multigraph with one edge per adjacency entry, and let $s$ be a vertex such that the
source of every edge of $G$ is reachable from $s$. Then $G$ has an Euler circuit from $s$ if and
only if $G$ is balanced, that is, every vertex is the source of exactly as many edge occurrences
as it is the target of.

## Sources

- CLRS, third edition, Problem 22-3; strong connectivity is weakened to reachability from $s$ of the source of every edge.
