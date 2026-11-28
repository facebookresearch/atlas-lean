# Conservative coalescing after simplification

Let $G$ be a finite undirected graph and $k \ge 1$. Suppose that the [simplification procedure](removing-a-low-degree-node-preserves-colorability.md), which repeatedly removes a vertex of degree less than $k$, empties $G$. Let $G_0$ be obtained from $G$ by some rounds of simplification, and let $G_0'$ be obtained from $G_0$ by [conservative coalescing](briggs-s-conservative-coalescing.md) of two non-adjacent vertices whose coalesced vertex has fewer than $k$ significant neighbors in $G_0'$. Then the graph obtained from $G$ by performing the same coalescing is emptied by simplification. So interleaving simplification and conservative coalescing never introduces a spill.

**Proof.** Simplification empties $G_0$, an induced subgraph of $G$, so by [conservative coalescing](briggs-s-conservative-coalescing.md) it empties $G_0'$. The vertices removed before reaching $G_0$ had degree less than $k$ when removed, which coalescing two vertices of $G_0$ does not increase, and they are colored after all vertices of $G_0'$; so removing them first and then emptying $G_0'$ empties the coalesced version of $G$.

## Depends on

- [Briggs's conservative coalescing](briggs-s-conservative-coalescing.md)
- [Removing a low-degree node preserves colorability](removing-a-low-degree-node-preserves-colorability.md)

## Sources

- L. George and A. W. Appel, "Iterated register coalescing", *ACM Transactions on Programming Languages and Systems* 18(3):300–324, 1996, <https://www.cs.cmu.edu/afs/cs/academic/class/15745-s07/www/papers/george.pdf>, Section 5: the iterated algorithm of Figure 5 (build, simplify, coalesce, freeze, select) and the theorem that conservative coalescing on an intermediate graph produced after some rounds of simplification produces a colorable graph, with its proof.
