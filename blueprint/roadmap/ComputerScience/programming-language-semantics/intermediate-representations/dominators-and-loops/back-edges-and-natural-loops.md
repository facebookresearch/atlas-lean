# Back edges and natural loops

Let $G$ be a control-flow graph with a start node from which every node is reachable, with the [dominance relation](../dominance-and-static-single-assignment-form.md) $\mathrm{dom}$.

- An edge $n \to h$ is a *back edge* if $h$ dominates $n$, and a *forward edge* if $n$ dominates $h$.
- The *natural loop* of a back edge $n \to h$ is the set consisting of $h$ and of the nodes that are dominated by $h$ and can reach $n$ by a path that does not pass through $h$. Its *header* is $h$.

A natural loop is strongly connected, and every edge entering it from outside ends at its header. Every *loop*, a strongly connected set of nodes that contains a cycle of at least one edge (for a single node, an edge from the node to itself) and is entered only through one node, contains at least one back edge. The natural loop of a back edge $n \to h$ is found by a search backward from $n$ along reversed edges that stops at $h$; the nodes reached that are dominated by $h$ form the loop.

## Depends on

- [Dominance and static single assignment form](../dominance-and-static-single-assignment-form.md)

## Sources

- A. C. Myers, *Control-flow analysis*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/cflow/index.html>: sections "Definition of a loop" (a strongly connected set of nodes entered only through its header), "Dominators" (forward and back edges), "Natural loops" (the natural loop of a back edge $n \to h$) and "Finding natural loops and control trees" (the backward search from $n$ stopped at $h$).
