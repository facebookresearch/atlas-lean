# Construction of minimal SSA form

Let the control-flow graph of a program have an entry node that has no predecessors and from which every node is reachable. Every such program can be put into minimal SSA form, in the sense of [translation to SSA form](translation-to-static-single-assignment-form.md), by computing the [dominance frontiers](../dominance-frontiers.md), placing a $\varphi$-function for each variable $V$ at every node of $\mathrm{DF}^+(S_V)$, where $S_V$ is the set of nodes that assign to $V$ together with the entry node, and then renaming. Let $E$ be the number of edges of the control-flow graph, $A_{\mathrm{tot}}$ the number of assignments to variables in the resulting program (each target of an ordinary assignment and each $\varphi$-function counting once), $M_{\mathrm{tot}}$ the number of mentions of variables in it, and $A_{\mathrm{tot}}(X)$ the number of these assignments in the node $X$. Given the dominator tree, the whole construction runs in time

$$O\Bigl(N + E + \sum_X |\mathrm{DF}(X)| + \sum_X A_{\mathrm{tot}}(X)\,|\mathrm{DF}(X)| + M_{\mathrm{tot}}\Bigr),$$

with $N$ the number of nodes; as $N \le E + 1$, this is the source's bound whenever $E \ge 1$. The source writes the third term as $A_{\mathrm{tot}} \cdot \mathrm{avrgDF}$, with $\mathrm{avrgDF}$ the average of $|\mathrm{DF}(X)|$ weighted by $A_{\mathrm{tot}}(X)$; the sum is the same quantity and is also defined when $A_{\mathrm{tot}} = 0$.

**Proof idea.** By [the characterization of φ-placement](../iterated-dominance-frontiers-are-iterated-joins.md) the placement satisfies condition 1 with the fewest $\varphi$-functions. Condition 2 follows from [the uniqueness of assignments](each-renamed-variable-has-exactly-one-assignme.md) and condition 3 from [the preservation of values](renaming-preserves-the-values-of-variables.md). The time bound adds the costs of computing the frontiers from the dominator tree, of the worklist placement, and of the renaming walk, which takes time $O(N + E + M_{\mathrm{tot}})$. The source also counts the computation of the dominator tree in the first term, under the convention of its footnote 4 for the inverse Ackermann factor of Lengauer and Tarjan; that cost is not part of the bound stated here.

## Depends on

- [Translation to static single assignment form](translation-to-static-single-assignment-form.md)
- [Dominance frontiers](../dominance-frontiers.md)

## Proof depends on

- [Iterated dominance frontiers are iterated joins](../iterated-dominance-frontiers-are-iterated-joins.md)
- [Each renamed variable has exactly one assignment](each-renamed-variable-has-exactly-one-assignme.md)
- [Renaming preserves the values of variables](renaming-preserves-the-values-of-variables.md)
- [Computing dominance frontiers bottom up](../computing-dominance-frontiers-bottom-up.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 5: Figure 11 (placing $\varphi$-functions with a worklist), Figure 12 (renaming), equation (7) (the weighted average $\mathrm{avrgDF}$) and Theorem 3 with its proof.
