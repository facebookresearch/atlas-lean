# George's coalescing criterion

Let $G$ be a finite undirected graph and $k \ge 1$, and let $a$ and $b$ be non-adjacent vertices such that every neighbor $t$ of $a$ is adjacent to $b$ or has degree less than $k$. Let $G'$ be obtained by coalescing $a$ and $b$ into one vertex adjacent to the union of their neighborhoods. If the [simplification procedure](removing-a-low-degree-node-preserves-colorability.md) empties $G$, then it empties $G'$.

**Proof.** In $G'$ a neighbor $t$ of $a$ that is not adjacent to $b$ loses the neighbor $a$ and gains the coalesced vertex, so its degree stays below $k$; remove these vertices first. What remains is isomorphic to the subgraph of $G$ induced by the vertices other than $a$ and the removed ones, with the coalesced vertex in the role of $b$, because all remaining neighbors of $a$ were already neighbors of $b$. Simplification empties every induced subgraph of $G$.

The criterion suits coalescing a temporary $a$ into a precolored machine register $b$, whose neighborhood need not be traversed.

## Depends on

- [Removing a low-degree node preserves colorability](removing-a-low-degree-node-preserves-colorability.md)

## Sources

- L. George and A. W. Appel, "Iterated register coalescing", *ACM Transactions on Programming Languages and Systems* 18(3):300–324, 1996, <https://www.cs.cmu.edu/afs/cs/academic/class/15745-s07/www/papers/george.pdf>, Section 6: the heuristic for coalescing a pseudoregister $X$ with a machine register $R$, which is allowed if every neighbor $T$ of $X$ already interferes with $R$, is a machine register, or has degree less than $K$, so that no neighbor's number of significant-degree neighbors rises from below $K$ to $K$ or more. The proof above is written out here.
