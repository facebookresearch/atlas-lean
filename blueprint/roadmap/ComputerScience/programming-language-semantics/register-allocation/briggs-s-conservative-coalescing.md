# Briggs's conservative coalescing

Let $G$ be a finite undirected graph, $k \ge 1$, and call a vertex *significant* if its degree is at least $k$. *Coalescing* two non-adjacent vertices $a$ and $b$ replaces them by one vertex $ab$ adjacent to the union of their neighborhoods.

**Theorem.** Suppose that $ab$ has fewer than $k$ significant neighbors in the coalesced graph $G'$. If the [simplification procedure](removing-a-low-degree-node-preserves-colorability.md), which repeatedly removes a vertex of degree less than $k$, empties $G$, then it also empties $G'$. In particular coalescing such a pair never turns a graph that simplification colors with $k$ colors into one that it does not.

**Proof.** Simplification empties a graph exactly when every nonempty subgraph has a vertex of degree less than $k$, a property inherited by subgraphs, since removing a vertex never raises a degree. Run simplification on $G'$, first removing the neighbors of $ab$ that have degree less than $k$. Afterwards $ab$ has only significant neighbors left, fewer than $k$ of them, so it can be removed. What remains is an induced subgraph of $G$ that contains neither $a$ nor $b$, so simplification empties it.

Applied to the interference graph, the criterion lets an allocator delete a move between $a$ and $b$ without causing a spill that simplification would otherwise avoid.

## Depends on

- [Removing a low-degree node preserves colorability](removing-a-low-degree-node-preserves-colorability.md)
- [Interference graphs](interference-graphs.md)

## Sources

- A. C. Myers, *Register Allocation*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/regalloc/index.html>: section "Conservative Coalescing" (Briggs's criterion: merge only when the merged node has fewer than $k$ high-degree neighbors, because after its low-degree neighbors are removed it is itself low-degree) and section "Graph coloring with coalescing". The proof above is written out here.
