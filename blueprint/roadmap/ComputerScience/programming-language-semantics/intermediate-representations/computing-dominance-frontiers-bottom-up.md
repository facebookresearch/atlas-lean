# Computing dominance frontiers bottom up

Let $G$ be a control-flow graph with $N$ nodes and $E$ edges and an entry node that has no predecessors and from which every node is reachable, with its dominator tree and the [dominance frontiers](dominance-frontiers.md) $\mathrm{DF}$. Visit the nodes in a bottom-up traversal of the dominator tree and, at a node $X$, compute

$$\mathrm{DF}(X) = \{Y \in \mathrm{Succ}(X) \mid \mathrm{idom}(Y) \ne X\} \cup \bigcup_{Z \in \mathrm{Children}(X)} \{Y \in \mathrm{DF}(Z) \mid \mathrm{idom}(Y) \ne X\}$$

from the successors of $X$ and the already computed frontiers of its children. This computes $\mathrm{DF}(X)$ for every node, in time $O(N + E + \sum_X |\mathrm{DF}(X)|)$, which is $O(E + N^2)$ in the worst case; since every node is reachable from the entry, $N \le E + 1$, and the bound is the source's $O(E + \sum_X |\mathrm{DF}(X)|)$ whenever $E \ge 1$.

**Proof.** The formula is correct by [the decomposition](dominance-frontier-decomposition.md) together with [the local test](local-test-for-dominance-frontiers.md) and [the upward test](upward-test-for-dominance-frontiers.md). Each successor edge and each element of a child's frontier is examined once.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)

## Proof depends on

- [Dominance frontier decomposition](dominance-frontier-decomposition.md)
- [Local test for dominance frontiers](local-test-for-dominance-frontiers.md)
- [Upward test for dominance frontiers](upward-test-for-dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 4.2: Figure 10 (the bottom-up algorithm), Theorem 1 (its correctness, from Lemmas 1–3) and the time bound $O(E + \mathrm{size}(\mathrm{DF}))$, $O(E + N^2)$ in the worst case.
