# Removing a low-degree node preserves colorability

Let $G$ be a finite undirected graph, $k \ge 1$, and $v$ a vertex of degree less than $k$. Then $G$ is $k$-colorable if and only if $G - v$ is. Every $k$-coloring of $G - v$ extends to $G$ by giving $v$ a color not used by any of its fewer than $k$ neighbors.

**Simplification.** Repeatedly removing a vertex of degree less than $k$, pushing it on a stack, and recoloring the removed vertices in reverse order therefore colors $G$ with $k$ colors whenever the removals empty the graph. Removing a vertex lowers the degrees of its neighbors, so new low-degree vertices can appear. If at some point every remaining vertex has degree at least $k$, the procedure decides nothing: the graph may or may not be $k$-colorable. Register allocators then remove a high-degree vertex optimistically, and spill it if no color is free when it is popped.

**Proof.** If $G$ is $k$-colorable, so is its subgraph $G - v$. Conversely, a $k$-coloring of $G - v$ uses fewer than $k$ colors on the neighbors of $v$, so a color remains for $v$.

## Depends on

- [Interference graphs](interference-graphs.md)

## Sources

- A. C. Myers, *Register Allocation*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/regalloc/index.html>: section "Graph Coloring and Kempe's Heuristic" (low-degree and high-degree nodes, removing a low-degree node reduces the problem to a simpler graph whose coloring leaves a color for it, the stack of removed nodes) and section "Optimistic coloring" (graphs with no low-degree node may or may not be colorable; optimistic removal and spilling).
