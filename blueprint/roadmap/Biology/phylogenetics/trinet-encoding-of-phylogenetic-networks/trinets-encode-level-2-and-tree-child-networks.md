# Trinets encode level-2 and tree-child networks

Use the definitions of [trinets and cut-arc sets](trinets-and-cut-arc-sets.md): networks are rooted phylogenetic networks on $X$ with no in-degree-$1$ out-degree-$1$ vertices and a root of out-degree at least $2$, identified up to leaf-label-preserving isomorphism; $\mathrm{Tn}(N)$ is the set of trinets exhibited by a binary network $N$ on $X$; and $N$ is *encoded* by its trinets if no recoverable network $N' \ne N$ on $X$ satisfies $\mathrm{Tn}(N') = \mathrm{Tn}(N)$.

**Theorem.** Let $|X| \ge 3$.

1. Every binary, simple level-2 network on $X$ is encoded by its trinets.
2. Every binary recoverable level-2 network on $X$ is encoded by its trinets.
3. Every binary tree-child network on $X$ (a network in which every non-leaf vertex has a child that is not a reticulation; such networks have no redundant biconnected components, so they are recoverable) is encoded by its trinets.
4. More generally, every binary recoverable network on $X$ each of whose biconnected components has at most two reticulations, or is tree-child, or has at most three outgoing cut-arcs, is encoded by its trinets.

Level-1 networks were already known to be encoded by their trinets. By contrast, rooted triplets do not encode networks, and distinct tree-child networks can display exactly the same set of trees, so the trinet statement is strictly stronger than encoding by displayed trees.

## Depends on

- [Trinets and cut-arc sets of a phylogenetic network](trinets-and-cut-arc-sets.md)

## Expansion

By the decomposition theorem of [trinets and cut-arc sets](trinets-and-cut-arc-sets.md) it suffices to treat simple networks. A simple binary level-2 network is obtained from one of the finitely many level-2 *generators* by hanging leaves on its *sides*: subdividing a generator arc and attaching a leaf to each new vertex, or attaching a leaf to a reticulation sink of the generator (an in-degree-$2$ out-degree-$0$ vertex). The proof shows case by case that the trinets containing a leaf on each side of a small set of crucial sides determine the generator and the side of every leaf, and the decomposition theorem lifts this to all recoverable level-2 networks. For tree-child networks the proof is an induction on the level. It removes a leaf $x$ of maximal distance from the root, whose parent is a reticulation $r$ whose two parents are not joined by an arc, and locates each parent of $r$ from trinets. The needed lowest common ancestors are produced by two local facts, not by a global uniqueness property. If $(u, v)$ is an arc into a reticulation $v$ with no directed path from $u$ to the other parent of $v$, and there are tree paths (paths with no reticulation after their first vertex) from $u$ to a leaf $x'$ and from $v$ to a leaf $y'$, then $x' \ne y'$ and $u$ is their unique lowest common ancestor. And a lowest common ancestor of two leaves that is already unique in $N$ remains in, and is the unique lowest common ancestor in, every exhibited trinet containing both leaves. Item 4 combines the three cases through the decomposition theorem, since components with at most three outgoing arcs are visible in a single trinet.

## Sources

- L. van Iersel and V. Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", Journal of Mathematical Biology 68 (2014), <https://doi.org/10.1007/s00285-013-0683-5> (arXiv:1210.0362). Section 2 (Observation 3), Theorem 3 and Corollary 1 (Section 4), Observations 8–9 and Theorem 4 (Section 5), Corollary 2 (Section 6).
