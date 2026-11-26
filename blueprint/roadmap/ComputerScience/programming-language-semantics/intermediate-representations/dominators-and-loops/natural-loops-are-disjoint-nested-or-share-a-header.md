# Natural loops are disjoint, nested or share a header

Let $G$ be a control-flow graph with a start node from which every node is reachable. If two [natural loops](back-edges-and-natural-loops.md) of $G$ have different headers, then they are disjoint or one of them is contained in the other. So two natural loops that intersect without being nested have the same header; merging the natural loops that share a header leaves a family of loops any two of which are disjoint or nested, and inclusion makes this family a forest, the *control tree* of $G$.

**Proof.** Let $L_1$ and $L_2$ be the natural loops of back edges $n_1 \to h_1$ and $n_2 \to h_2$ with $h_1 \ne h_2$, and let $x \in L_1 \cap L_2$. Both headers dominate $x$, so one dominates the other, say $h_1$ dominates $h_2$. Every node of $L_2$ is dominated by $h_2$, hence by $h_1$. The node $h_1$ is not in $L_2$, since otherwise $h_2$ would dominate $h_1$; in particular $x \ne h_1$. The node $h_2$ is in $L_1$: there is a path from $h_2$ to $x$ inside $L_2$ and from $x$ to $n_1$ avoiding $h_1$, and the first path avoids $h_1$ because $h_1 \notin L_2$. Each node $y$ of $L_2$ reaches $n_2$, and then $h_2$, inside $L_2$, so without passing through $h_1$, and then reaches $n_1$ through $h_2 \in L_1$ without passing through $h_1$. So $L_2 \subseteq L_1$.

## Depends on

- [Back edges and natural loops](back-edges-and-natural-loops.md)

## Sources

- A. C. Myers, *Control-flow analysis*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/cflow/index.html>: section "Finding natural loops and control trees" (two natural loops can be disjoint or nested, or intersect without being nested only if they share the same header; merging such loops makes all loops disjoint or nested, and subset inclusion gives the control tree). The proof above is written out here.
