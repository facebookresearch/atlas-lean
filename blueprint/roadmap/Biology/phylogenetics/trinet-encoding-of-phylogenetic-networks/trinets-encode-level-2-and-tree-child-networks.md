# Trinets encode level-2 and tree-child networks

Use the definitions of [trinets and cut-arc sets](trinets-and-cut-arc-sets.md): $\mathrm{Tn}(N)$ is the set of trinets exhibited by a rooted binary phylogenetic network $N$ on $X$, and $N$ is *encoded* by its trinets if no recoverable network $N' \ne N$ satisfies $\mathrm{Tn}(N') = \mathrm{Tn}(N)$.

**Theorem.** Let $|X| \ge 3$.

1. Every binary, simple level-2 network on $X$ is encoded by its trinets.
2. Every binary recoverable level-2 network on $X$ is encoded by its trinets.
3. Every binary tree-child network on $X$ is encoded by its trinets.
4. More generally, every binary recoverable network on $X$ each of whose biconnected components has at most two reticulations, or is tree-child, or has at most three outgoing cut-arcs, is encoded by its trinets.

Level-1 networks were already known to be encoded by their trinets. By contrast, rooted triplets do not encode networks, and distinct tree-child networks can display exactly the same set of trees, so the trinet statement is strictly stronger than encoding by displayed trees.

## Depends on

- [Trinets and cut-arc sets of a phylogenetic network](trinets-and-cut-arc-sets.md)
## Expansion

By the decomposition theorem it suffices to treat simple networks. A simple binary level-2 network is obtained from one of the finitely many level-2 *generators* by hanging leaves on its arcs; the proof shows case by case that the trinets determine the generator and the positions of the leaves, and the decomposition theorem lifts this to all recoverable level-2 networks. For tree-child networks the proof is an induction on the level: in a tree-child network every vertex has a tree path to a leaf, so lowest common ancestors of leaf pairs are unique and survive in exhibited trinets, which lets one identify a removable reticulation from trinets alone and apply the induction hypothesis. Item 4 combines the three cases through the decomposition theorem, since components with at most three outgoing arcs are visible in a single trinet.

## Sources

- L. van Iersel and V. Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", Journal of Mathematical Biology 68 (2014), <https://doi.org/10.1007/s00285-013-0683-5>. Theorem 3 and Corollary 1 (Section 4), Theorem 4 (Section 5), Corollary 2 (Section 6).
