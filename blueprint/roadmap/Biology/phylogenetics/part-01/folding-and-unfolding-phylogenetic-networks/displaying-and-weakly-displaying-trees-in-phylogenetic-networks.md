# Displaying and weakly displaying trees in phylogenetic networks

**Definitions.** A phylogenetic tree $T$ on $X$ is *displayed* by a phylogenetic network $N$ on $X$ if $T$ can be obtained from a subtree of $N$ by suppressing vertices of in- and out-degree one (equivalently, by choosing one incoming arc at each reticulation and deleting unneeded parts). It is *weakly displayed* by $N$ if it is displayed by the unfolding $U(N)$, a MUL-tree, in the sense that some copy of each leaf label can be chosen so that the induced subtree of $U(N)$ is a subdivision of $T$. An *$X$-morphism* $f = (f_V, f_A)$ between rooted graphs on $X$ sends vertices to vertices and arcs to arcs, compatibly with tails and heads ($f_A(u, w) = (f_V(u), f_V(w))$), and keeps leaf labels; a *folding map* $f : T \to N$ from a (pseudo) MUL-tree is an $X$-morphism with $f_V$ and $f_A$ surjective that has unique arc lifting: for every vertex $v$ of $T$, $f_A$ maps the out-arcs of $v$ bijectively onto the out-arcs of $f_V(v)$ (a phylogenetic analogue of a graph opfibration).

**Theorems.**

1. *Universal cover.* The map $U^*(N) \to N$ sending each root path to its last vertex is a folding map; every $X$-morphism $g : T' \to N$ from a pseudo MUL-tree lifts through any folding map $f : T \to N$ to an $X$-morphism $\tilde g$ with $f \circ \tilde g = g$, uniquely when $g$ is rooted. Hence any pseudo MUL-tree with a folding map onto $N$ is isomorphic to $U^*(N)$.
2. *Hardness of displaying.* Deciding whether a binary phylogenetic tree is displayed by a network is NP-complete even for binary, compressed tree-sibling networks, and hence for stable networks.
3. *Weak displaying.* $T$ is weakly displayed by $N$ if and only if there is a *locally separated reconciliation* between $T$ and $N$: a map $r$ from the vertices of $T$ to $V_{tr}(N)$, the tree vertices of $N$ together with its root, with $r(x) = x$ for every leaf $x$, assigning to each arc $(u, v)$ of $T$ a directed path of $N$ from $r(u)$ to $r(v)$, such that for every vertex $v$ of $T$ with children $v_1, v_2$ the paths assigned to $(v, v_1)$ and $(v, v_2)$ each contain at least one arc and start with different arcs.
4. *Algorithm.* Weak displaying of a binary tree $T$ by $N$ can be decided by dynamic programming in $O(|X| \cdot |V(N)| \cdot \max_{v \in V(N)} |ch(v)|)$ time.

## Depends on

- [Stable phylogenetic networks and their characterization](stable-phylogenetic-networks-and-their-characterization.md)

## Expansion

The lifting property is path lifting for covering spaces: start at a preimage of the image of the root and extend the lift arc by arc, using local out-isomorphism of the folding map to choose the unique lifted arc. For hardness, a reduction from tree displaying in general binary networks (known NP-complete) attaches gadgets that make the network compressed and tree-sibling while preserving the answer; by the characterization of stable networks the problem stays hard there. Weak displaying relaxes displaying because different copies of a leaf in $U(N)$ may use different routes through the same reticulation: a locally separated reconciliation lifts, by the universal-cover property, to an embedding of a subdivision of $T$ into $U(N)$, and conversely. Since a binary tree has $2|X| - 1$ vertices, a table indexed by pairs (tree vertex, network vertex) filled bottom-up gives the polynomial bound, in contrast with the NP-completeness of ordinary displaying.

## Sources

- K. T. Huber, V. Moulton, M. Steel, T. Wu, "Folding and unfolding phylogenetic trees and networks", Journal of Mathematical Biology (2016), Section 5 (Theorems 2–4, Corollaries 2–3), Section 6 (Theorem 5) and Section 7 (Theorem 6, Corollary 4). <https://doi.org/10.1007/s00285-016-0993-5> (PMC5061860).
