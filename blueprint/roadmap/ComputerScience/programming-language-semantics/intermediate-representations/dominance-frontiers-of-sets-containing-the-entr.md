# Dominance frontiers of sets containing the entry are joins

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable. For every set $S$ of nodes that contains the entry node,

$$\mathrm{DF}(S) \subseteq J(S),$$

with the [dominance frontier](dominance-frontiers.md) $\mathrm{DF}$ and the [join set](converging-paths-and-join-sets.md) $J$.

**Proof.** Let $X \in S$ and $Y \in \mathrm{DF}(X)$. There is a path from $X$ to $Y$ all of whose nodes before $Y$ are dominated by $X$, and a path from the entry to $Y$ none of whose nodes before $Y$ is dominated by $X$. These paths converge at $Y$.

The hypothesis on the entry is needed: if the entry $E$ had a predecessor $A$ with an edge $A \to E$, then $E \in \mathrm{DF}(\{E\})$ while $J(\{E\}) = \emptyset$.

## Depends on

- [Converging paths and join sets](converging-paths-and-join-sets.md)
- [Dominance frontiers](dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 2 (the control-flow graph, whose edges leave the entry node and never enter it) and Section 4.3 (Lemma 7 with its proof).
