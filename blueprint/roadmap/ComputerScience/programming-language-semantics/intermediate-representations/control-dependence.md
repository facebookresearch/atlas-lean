# Control dependence

Let $G$ be a control-flow graph with an entry node and an exit node, in which every node is reachable from the entry and reaches the exit.

- A node $X$ *postdominates* a node $Y$ if $X$ lies on every path from $Y$ to the exit. Postdominance is reflexive and transitive, and $X$ *strictly* postdominates $Y$ if moreover $X \ne Y$. Postdominance in $G$ is dominance in the *reverse graph*, which has an edge $Y \to X$ for each edge $X \to Y$ of $G$ and the roles of entry and exit exchanged.
- A node $Y$ is *control dependent* on a node $X$ if there is a nonnull path from $X$ to $Y$ such that $Y$ postdominates every node after $X$ on it, and $Y$ does not strictly postdominate $X$. So some edge leaving $X$ forces $Y$ to execute, while some path from $X$ avoids $Y$.

The first condition is equivalent to: $Y$ postdominates a successor of $X$.

## Depends on

- [Dominance and static single assignment form](dominance-and-static-single-assignment-form.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 6: the definitions of postdominance, strict and immediate postdominance and control dependence, the reverse control flow graph, and Lemma 11.
- A. C. Myers, *Reaching definitions and SSA*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/reachdef/index.html>: section "Postdominators".
