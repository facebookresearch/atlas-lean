# Local test for dominance frontiers

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable, and let $\mathrm{DF}_{\mathrm{local}}$ be the local part of the [dominance frontier](dominance-frontiers.md). For every node $X$,

$$\mathrm{DF}_{\mathrm{local}}(X) = \{Y \in \mathrm{Succ}(X) \mid \mathrm{idom}(Y) \ne X\}.$$

**Proof.** Let $Y$ be a successor of $X$. Every strict dominator of $Y$ lies on every path from the entry to $X$ followed by the edge $X \to Y$, so it dominates $X$. Hence, if $X$ strictly dominates $Y$, then $X$ is the strict dominator of $Y$ closest to $Y$, that is, $\mathrm{idom}(Y) = X$; the converse is immediate.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 4.2: Lemma 2, the local test for $\mathrm{DF}_{\mathrm{local}}$, with its proof.
