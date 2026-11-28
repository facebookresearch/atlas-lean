# Renamed variables along an edge without a φ-function

Run the renaming step of [translation to SSA form](translation-to-static-single-assignment-form.md) after placing $\varphi$-functions at the [iterated dominance frontiers](../dominance-frontiers.md) of the assignments to each variable. For a variable $V$ and a node $X$, let $\mathrm{TopAfter}(V, X)$ be $V_i$ for $i$ the top of $S(V)$ after all statements of $X$, its $\varphi$-functions included, have been processed. For every variable $V$ and every edge $X \to Y$ such that $Y$ has no $\varphi$-function for $V$,

$$\mathrm{TopAfter}(V, X) = \mathrm{TopAfter}(V, \mathrm{idom}(Y)).$$

**Proof idea.** Assume $X \ne \mathrm{idom}(Y)$, the other case being trivial. No node with $Y$ in its dominance frontier assigns to a variable derived from $V$. By the [local test](../local-test-for-dominance-frontiers.md), $X$ does not, so $\mathrm{TopAfter}(V, X)$ is inherited from the first strict dominator $U$ of $X$ that does. Then $Y \notin \mathrm{DF}(U)$, and since $U$ dominates the predecessor $X$ of $Y$, $U$ strictly dominates $Y$. Every node $Z$ after $U$ on the dominator-tree path from $U$ down to $\mathrm{idom}(Y)$, $\mathrm{idom}(Y)$ itself included, also dominates $X$, so it does not assign to such a variable, and both sides equal $\mathrm{TopAfter}(V, U)$.

## Depends on

- [Translation to static single assignment form](translation-to-static-single-assignment-form.md)
- [Dominance frontiers](../dominance-frontiers.md)

## Proof depends on

- [Local test for dominance frontiers](../local-test-for-dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 5.2: the definition of $\mathrm{TopAfter}$, and Lemma 9 with its proof.
