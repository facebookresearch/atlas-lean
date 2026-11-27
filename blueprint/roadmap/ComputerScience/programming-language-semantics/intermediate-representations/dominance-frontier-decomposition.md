# Dominance frontier decomposition

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable, with its dominator tree and the [dominance frontiers](dominance-frontiers.md) $\mathrm{DF}$, $\mathrm{DF}_{\mathrm{local}}$ and $\mathrm{DF}_{\mathrm{up}}$. For every node $X$,

$$\mathrm{DF}(X) = \mathrm{DF}_{\mathrm{local}}(X) \cup \bigcup_{Z \in \mathrm{Children}(X)} \mathrm{DF}_{\mathrm{up}}(Z),$$

where $\mathrm{Children}(X)$ is the set of children of $X$ in the dominator tree.

**Proof.** The right-hand side is contained in $\mathrm{DF}(X)$: $\mathrm{DF}_{\mathrm{local}}(X) \subseteq \mathrm{DF}(X)$ because $X$ dominates itself, and if $Y \in \mathrm{DF}_{\mathrm{up}}(Z)$ for a child $Z$, then $X$ dominates $Z$, which dominates a predecessor of $Y$, while $X = \mathrm{idom}(Z)$ does not strictly dominate $Y$. Conversely, let $Y \in \mathrm{DF}(X)$ and let $X$ dominate the predecessor $U$ of $Y$. If $U = X$, then $Y \in \mathrm{DF}_{\mathrm{local}}(X)$. Otherwise the child $Z$ of $X$ on the dominator-tree path from $X$ to $U$ dominates $U$; it does not strictly dominate $Y$, for then $X$ would, so $Y \in \mathrm{DF}(Z)$ and hence $Y \in \mathrm{DF}_{\mathrm{up}}(Z)$.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 4.2: equation (4) and Lemma 1 with its proof.
