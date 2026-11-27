# Control dependence from reverse dominance frontiers

Let $G$ be a control-flow graph with $E$ edges, an entry node and an exit node that has no successors, in which every node is reachable from the entry and reaches the exit, and let $\mathrm{RDF}$ be the [dominance frontier](dominance-frontiers.md) mapping of its reverse graph.

1. A node $Y$ is [control dependent](control-dependence.md) on a node $X$ if and only if $X \in \mathrm{RDF}(Y)$.
2. Consequently, the sets $\mathrm{CD}(X)$ of nodes control dependent on each $X$ are obtained by computing $\mathrm{RDF}$ and inverting it, in time $O(N + E + \sum_Y |\mathrm{RDF}(Y)|)$, with $N$ the number of nodes, once the dominator tree of the reverse graph is known; the exit, which has no predecessors in the reverse graph, is its entry, as the bottom-up computation of frontiers requires.

**Proof.** By [the successor lemma](postdominating-a-successor.md), the first condition is equivalent to postdominating a successor, so $Y$ is control dependent on $X$ if and only if $Y$ postdominates a successor of $X$ but does not strictly postdominate $X$. In the reverse graph this says that $Y$ dominates a predecessor of $X$ but does not strictly dominate $X$, that is, $X \in \mathrm{RDF}(Y)$.

## Depends on

- [Control dependence](control-dependence.md)
- [Dominance frontiers](dominance-frontiers.md)

## Proof depends on

- [Postdominating a successor](postdominating-a-successor.md)
- [Computing dominance frontiers bottom up](computing-dominance-frontiers-bottom-up.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 6: Lemma 11, Corollary 1 and its proof, Figure 14 (computing $\mathrm{CD}$ by inverting $\mathrm{RDF}$) and the time bound $O(E + \mathrm{size}(\mathrm{RDF}))$ after the dominator tree of the reverse graph is built.
