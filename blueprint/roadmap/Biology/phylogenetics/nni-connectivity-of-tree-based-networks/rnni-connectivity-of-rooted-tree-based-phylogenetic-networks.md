# rNNI connectivity of rooted tree-based phylogenetic networks

**Definitions.** A (binary) **rooted phylogenetic network** on a leaf set $X$ is a simple directed acyclic graph with a single root (in-degree $0$, out-degree $1$ or $2$), leaves (in-degree $1$, out-degree $0$) labelled bijectively by $X$, tree vertices (in-degree $1$, out-degree $2$) and reticulations (in-degree $2$, out-degree $1$). It is **tree-based** if it has a spanning tree $T$ (a *support tree*) whose leaves are exactly the leaves of the network; equivalently, it is a rooted $X$-tree with extra arcs joining subdivision points of its edges. The number of reticulations $k$ is the network's *tier*.

A **rooted nearest neighbour interchange** (rNNI) move on arcs on $\{a,b\}, \{b,c\}, \{c,d\}$ replaces them by arcs on $\{a,c\}, \{b,c\}, \{b,d\}$. The move must keep the in- and out-degrees of $a$ and $d$, keep those of $b$ and $c$ in $\{1, 2\}$, and leave an acyclic phylogenetic network; it does not change the tier. A **tail move** of an arc $e = (u,v)$ to an arc $f$ deletes $e$, subdivides $f$ with a new vertex $u'$, suppresses $u$ and adds $(u', v)$. It has distance $1$ when $f$ is adjacent to $e$.

**Lemma (moves that preserve tree-basedness).** Let $N$ be tree-based with support tree $T$, let $u \to v \to w \to z$ be a path in $T$, and let $e, f$ be arcs of $N$ off this path incident to $v$ and $w$. The rNNI move swapping the attachment points of $e$ and $f$ is valid and yields a tree-based network if any of the following holds:

- $f$ points away from $w$ and $e \ne vz$;
- $e$ points towards $v$ and $f \ne uw$;
- $f \ne uw$, $e \ne vz$, and $N$ has no directed path from the target of $e$ to the source of $f$.

A similar statement handles moves at the root.

**Theorem (connectivity).** For every leaf set $X$ and every $k \ge 0$, the space of rooted tree-based networks on $X$ with $k$ reticulations is connected under rNNI moves: any two such networks are joined by a sequence of rNNI moves through tree-based networks.

**Theorem (tail moves).** The same space is connected under distance-$1$ tail moves.

## Expansion

The proof routes every network to a canonical form. A **burl-rooted tree** of tier $k$ has a path $\rho, b_1, \dots, b_k, \ell_1$ from the root through all $k$ reticulations to one leaf, while every other root-to-leaf path starts $\rho, a_1, \dots, a_k$ through tree vertices, with arcs $(a_i, b_i)$. All reticulations thus sit in a ladder-like "burl" next to the root, and below it hangs an ordinary rooted tree on $X \setminus \{\ell_1\}$. Burl-rooted trees of a fixed tier are connected under rNNI, because rNNI moves restricted to the tree part are classical rooted NNI moves, which connect rooted tree space, and leaves can be exchanged into the burl. Starting from any tree-based network with a fixed support tree, the lemma supplies moves that push reticulation arcs step by step towards the root while preserving a support tree, until the burl-rooted form is reached. Each such rNNI is either already a distance-1 tail move or can be simulated by two of them, which gives the tail-move theorem. Connectivity guarantees that local search over tree-based networks, for example in MCMC or heuristic network inference, can in principle reach every network of the tier.

## Sources

- Péter L. Erdős, Andrew Francis and Tamás Róbert Mezei, "Rooted NNI moves on tree-based phylogenetic networks", arXiv (2020), Section 2 (Definitions 2.1–2.3), Section 3 (Lemmas 3.1 and 3.3), Section 4 (Lemma 4.1, Theorems 4.2 and 4.3), <https://doi.org/10.48550/arXiv.2003.07283>.
- P. Gambette, L. van Iersel, M. Jones, M. Lafond, F. Pardi and C. Scornavacca, "Rearrangement moves on rooted phylogenetic networks", PLoS Computational Biology 13 (2017), e1005611, <https://doi.org/10.1371/journal.pcbi.1005611>.
