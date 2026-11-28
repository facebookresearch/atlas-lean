# Short-quartet coverage guarantees an exact strict consensus merger

**Short quartets.** Let $T$ be an unrooted binary tree on leaf set $S$ with positive edge weights $w$. For an internal edge $e$, deleting $e$ and its endpoints leaves four subtrees $A_1, \dots, A_4$; choosing in each $A_i$ a leaf $a_i$ closest to $e$ (in $w$-path length) gives a **short quartet** $\{a_1, a_2, a_3, a_4\}$ around $e$. The induced four-leaf trees on the short quartets of $(T, w)$ determine $T$.

**Strict consensus merger (SCM).** Two compatible unrooted binary source trees $t, t'$ are merged by restricting both to their common taxa (the *backbone*, the same tree for both by compatibility) and then reattaching the remaining taxa of each source tree onto the backbone edge on which they lie. If two source trees contribute taxa to the same backbone edge (a *collision*), the edge is subdivided once and all contributed subtrees are attached to the new vertex, which leaves the result unresolved. Several trees are merged two at a time.

**Theorem.** Let $t_1, \dots, t_k$ be unrooted binary trees with leaf sets $S_i$, and let $T$ be a binary tree on $\bigcup_i S_i$. Suppose
1. $S_i = A_i \cup X$ with $A_i \cap A_j = \emptyset$ for $i \ne j$ (all subsets share a common core $X$),
2. $t_i = T|_{S_i}$ (each source tree is correct), and
3. every short quartet of $T$ lies in some $S_i$.

Then SCM applied to $t_1, \dots, t_k$ returns $T$, whatever the order of merging.

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

It suffices to show that no backbone edge receives taxa from two source trees, since then every merge is uniquely determined and collision-free. The backbone on $X$ is fully resolved because all source trees agree with $T$. Fix a backbone edge $e$ and the maximal path $P = v_0, \dots, v_k$ of $T$ whose edges induce the same bipartition of $X$ as $e$; if two source trees contributed to $e$ then $k \ge 2$ and either some subtree $T_i$ hanging off $P$ contains taxa from two different $A_j$, or two adjacent hanging subtrees contain taxa from different $A_j$. In both cases there is a short quartet of $T$ containing $a \in A_j$ and $b \in A_l$ with $j \ne l$, and by hypothesis 3 some $S_i$ contains both, contradicting disjointness of the $A_i$. Divide-and-conquer methods (disk-covering decompositions, and DACTAL's padded recursive decomposition, which splits a current tree at a centroid edge into four parts and adds to each the $p/4$ leaves of every part nearest the edge as the shared set $X$) aim to make subsets small in evolutionary diameter while overlapping enough that all short quartets are covered; refinements of SCM such as SuperFine start from the SCM tree and so inherit the guarantee.

## Sources

- S. Nelesen, K. Liu, L.-S. Wang, C. R. Linder and T. Warnow, "DACTAL: divide-and-conquer trees (almost) without alignments", Bioinformatics 28 (2012), i274–i282, Section 2.1 (Theorem 1) and Section 2.2, <https://doi.org/10.1093/bioinformatics/bts218>, PMCID: PMC3371850.
- P. L. Erdős, M. A. Steel, L. A. Székely and T. J. Warnow, "A few logs suffice to build (almost) all trees (I)", Random Structures & Algorithms 14 (1999), 153–184.
