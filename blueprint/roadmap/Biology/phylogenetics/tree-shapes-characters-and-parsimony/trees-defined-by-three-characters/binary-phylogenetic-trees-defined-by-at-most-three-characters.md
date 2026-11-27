# Binary phylogenetic trees defined by at most three characters

**Setting.** A *character* on a set $X$ of taxa is a partition of $X$ (its parts are character states; the number of states is unbounded). A set $\mathcal C$ of characters is *convex* on an unrooted phylogenetic $X$-tree $T$ if, for every $\chi \in \mathcal C$, the minimal subtrees of $T$ spanning the different parts of $\chi$ are pairwise vertex-disjoint (each state arises once, with no parallel or reverse changes). $\mathcal C$ *defines* $T$ if it is convex on $T$ and on no other phylogenetic $X$-tree up to isomorphism. Semple and Steel showed that defining is equivalent to $\mathcal C$ being convex on $T$, distinguishing every internal edge, and its partition intersection graph $\mathrm{Int}(\mathcal C)$ (vertices are pairs $(\chi, A)$ with $A$ a part of $\chi$; edges join parts of different characters that intersect) having a unique minimal restricted chordal completion. Every binary phylogenetic tree is defined by four characters, and four can be necessary.

An *internal subtree* of $T$ is a subtree all of whose edges are internal (non-pendant). The **snowflake** is the 6-leaf tree with a central vertex whose three neighbors each have two further neighbors; the **3-star** is the tree with one center and three leaves.

**Theorem.** Let $T$ be a binary phylogenetic tree.
1. $T$ is defined by a set of at most three characters if and only if $T$ has no internal subtree isomorphic to the snowflake.
2. $T$ is defined by a set of at most two characters if and only if $T$ has no internal subtree isomorphic to the 3-star, i.e. if and only if $T$ is a caterpillar.

The smallest binary tree not defined by three characters has twelve leaves: it is the tree whose internal edges form exactly a snowflake.

## Expansion

A vertex incident with three internal edges cannot be resolved by two characters, since each internal edge must be "crossed" by some character and only two characters are available to separate three directions; caterpillars are defined by pairing consecutive cherries in two staggered ways. For three characters, the proof reduces to *internal 3-colorings*: color the internal edges with three colors so that each character is read off as the connected pieces of $T$ after removing edges of one color. Trees containing an internal snowflake are generated from the 12-leaf obstruction by cherry modifications that preserve non-definability (the partition intersection graph keeps two different minimal chordal completions); trees without an internal snowflake are built from small definable pieces by cherry modifications and cherry unions, along which a valid internal 3-coloring and the uniqueness of the chordal completion propagate.

## Sources

- Katharina T. Huber, Simone Linz, Vincent Moulton and Charles Semple, "Phylogenetic Trees Defined by at Most Three Characters", The Electronic Journal of Combinatorics 31 (2024), P4.42, <https://doi.org/10.37236/12560>; numbering as in arXiv:2311.09340: Section 1 (main theorem and its two-character analogue), Section 2 (Semple–Steel convexity and definability criteria, caterpillar theorem), Sections 3–5 (internal $k$-colorings and the two directions of the main theorem).
