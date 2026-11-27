# Dominance frontiers

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable, with the [dominance relation](dominance-and-static-single-assignment-form.md) and its dominator tree. The *dominance frontier* of a node $X$ is the set of nodes $Y$ such that $X$ dominates a predecessor of $Y$ but does not strictly dominate $Y$:

$$\mathrm{DF}(X) = \{Y \mid \exists P \in \mathrm{Pred}(Y).\ X \text{ dominates } P \text{ and } X \text{ does not strictly dominate } Y\}.$$

For a set $S$ of nodes, $\mathrm{DF}(S) = \bigcup_{X \in S} \mathrm{DF}(X)$. The *iterated dominance frontier* $\mathrm{DF}^+(S)$ is the limit of the increasing sequence $\mathrm{DF}_1 = \mathrm{DF}(S)$, $\mathrm{DF}_{i+1} = \mathrm{DF}(S \cup \mathrm{DF}_i)$.

Two auxiliary sets split the dominance frontier of a node along the dominator tree:
- the *local* part $\mathrm{DF}_{\mathrm{local}}(X) = \{Y \in \mathrm{Succ}(X) \mid X \text{ does not strictly dominate } Y\}$;
- for a node $Z$ other than the entry, the part passed up to its immediate dominator, $\mathrm{DF}_{\mathrm{up}}(Z) = \{Y \in \mathrm{DF}(Z) \mid \mathrm{idom}(Z) \text{ does not strictly dominate } Y\}$.

A node $X$ may lie in its own dominance frontier, as the header of a loop does.

## Depends on

- [Dominance and static single assignment form](dominance-and-static-single-assignment-form.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991: Section 4.2 (the definitions of $\mathrm{DF}$, $\mathrm{DF}_{\mathrm{local}}$ and $\mathrm{DF}_{\mathrm{up}}$) and Section 4.3 (dominance frontiers of sets and the iterated dominance frontier); Figure 9 shows a loop header in its own dominance frontier.
- A. C. Myers, *Reaching definitions and SSA*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/reachdef/index.html>: sections "Using dominators for SSA conversion" and "Computing the dominance frontier".
