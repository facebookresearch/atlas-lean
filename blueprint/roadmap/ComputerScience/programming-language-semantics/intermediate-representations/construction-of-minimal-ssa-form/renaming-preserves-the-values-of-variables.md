# Renaming preserves the values of variables

Translate a program by placing $\varphi$-functions at the [iterated dominance frontiers](../dominance-frontiers.md) of the assignments to each variable and running the renaming step of [translation to SSA form](translation-to-static-single-assignment-form.md). For a variable $V$ and a statement $A$, let $\mathrm{TopBefore}(V, A)$ be $V_i$ for $i$ the top of $S(V)$ just before $A$ is processed. Consider any control-flow path, followed in the original and in the transformed program, any variable $V$ and any occurrence along the path of a statement $A$ of the original program. Then the value of $V$ just before $A$ in the original program equals the value of $\mathrm{TopBefore}(V, A)$ just before $A$ in the transformed program. In particular, condition 3 of a translation to SSA form holds.

**Proof idea.** Induction along the path. Inside a node, the claim passes from one statement to the next by the semantics of assignment. At the first original statement of a node $Y$ entered by the edge $X \to Y$, $V$ agrees with $\mathrm{TopAfter}(V, X)$; if $Y$ has a $\varphi$-function for $V$, its operand for that edge is $\mathrm{TopAfter}(V, X)$, and otherwise [the edge lemma](renamed-variables-along-an-edge-without-a-phi.md) gives $\mathrm{TopAfter}(V, X) = \mathrm{TopAfter}(V, \mathrm{idom}(Y))$, which is $\mathrm{TopBefore}(V, A)$.

## Depends on

- [Translation to static single assignment form](translation-to-static-single-assignment-form.md)
- [Dominance frontiers](../dominance-frontiers.md)

## Proof depends on

- [Renamed variables along an edge without a φ-function](renamed-variables-along-an-edge-without-a-phi.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 5.2: the definitions of $\mathrm{TopBefore}$ and $\mathrm{TopAfter}$ for statements, Lemma 10 with its proof, and Figure 13.
