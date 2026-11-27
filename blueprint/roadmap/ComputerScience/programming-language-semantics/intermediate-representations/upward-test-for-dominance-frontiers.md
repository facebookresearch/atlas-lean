# Upward test for dominance frontiers

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable, with its dominator tree and the [dominance frontiers](dominance-frontiers.md) $\mathrm{DF}$ and $\mathrm{DF}_{\mathrm{up}}$. For every node $X$ and every child $Z$ of $X$ in the dominator tree,

$$\mathrm{DF}_{\mathrm{up}}(Z) = \{Y \in \mathrm{DF}(Z) \mid \mathrm{idom}(Y) \ne X\}.$$

**Proof idea.** For $Y \in \mathrm{DF}(Z)$ one shows that $X = \mathrm{idom}(Z)$ strictly dominates $Y$ exactly when $\mathrm{idom}(Y) = X$. If $X$ strictly dominated $Y$ with $\mathrm{idom}(Y) \ne X$, then $X$ would strictly dominate $\mathrm{idom}(Y)$; both $Z$ and $\mathrm{idom}(Y)$ dominate a common predecessor of $Y$, so they are comparable under dominance, and $\mathrm{idom}(Y)$ cannot strictly dominate $Z$, since $X$ is the immediate dominator of $Z$. So $Z$ would dominate $\mathrm{idom}(Y)$ and thus strictly dominate $Y$, contradicting $Y \in \mathrm{DF}(Z)$.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 4.2: Lemma 3, the upward test for $\mathrm{DF}_{\mathrm{up}}$, with its proof.
