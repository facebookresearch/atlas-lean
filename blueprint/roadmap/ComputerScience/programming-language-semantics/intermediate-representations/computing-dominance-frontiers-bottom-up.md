# Computing dominance frontiers bottom up

Let $G$ be a control-flow graph with $N$ nodes and $E$ edges, an entry node that has no predecessors and from which every node is reachable, and its dominator tree, and use the [dominance frontiers](dominance-frontiers.md) $\mathrm{DF}$, $\mathrm{DF}_{\mathrm{local}}$ and $\mathrm{DF}_{\mathrm{up}}$.

1. **Decomposition.** For every node $X$,

    $$\mathrm{DF}(X) = \mathrm{DF}_{\mathrm{local}}(X) \cup \bigcup_{Z \in \mathrm{Children}(X)} \mathrm{DF}_{\mathrm{up}}(Z),$$

    where the children are taken in the dominator tree.
2. **Local tests.** $\mathrm{DF}_{\mathrm{local}}(X) = \{Y \in \mathrm{Succ}(X) \mid \mathrm{idom}(Y) \ne X\}$, and for each child $Z$ of $X$, $\mathrm{DF}_{\mathrm{up}}(Z) = \{Y \in \mathrm{DF}(Z) \mid \mathrm{idom}(Y) \ne X\}$.
3. **Algorithm.** Visiting the nodes in a bottom-up traversal of the dominator tree and computing $\mathrm{DF}(X)$ from the successors of $X$ and the frontiers of its children with the tests of part 2 computes $\mathrm{DF}(X)$ for every node. It runs in time $O(E + \sum_X |\mathrm{DF}(X)|)$, which is $O(E + N^2)$ in the worst case.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 4.2: equation (4) and Lemma 1, Lemma 2, Lemma 3, Figure 10 (the bottom-up algorithm), Theorem 1 (its correctness) and the time bound $O(E + \mathrm{size}(\mathrm{DF}))$, $O(E + N^2)$ in the worst case.
