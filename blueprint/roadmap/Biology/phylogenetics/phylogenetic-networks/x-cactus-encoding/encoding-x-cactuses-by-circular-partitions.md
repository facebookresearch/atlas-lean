# Encoding X-cactuses by circular partitions

**Setting.** An *$X$-cactus* is a connected graph in which every edge lies in at most one cycle (a cactus), together with a labeling of vertices by a finite set $X$ of taxa such that every vertex of degree at most two carries at least one label. $X$-cactuses are phylogenetic networks generalizing $X$-trees. Deleting a cut edge splits $X$ into a bipartition; deleting the edges of a cycle splits $X$ into the label sets of the components hanging off the cycle, and the cycle orders these blocks cyclically, giving a *circular partition* of $X$. Let $\mathcal C(\mathcal N)$ be the set of all circular partitions arising from the cut edges and cycles of $\mathcal N$ (a bipartition is a circular partition with two blocks).

**Theorem.**
1. *(Encoding.)* A set $\mathcal C$ of circular partitions of $X$ equals $\mathcal C(\mathcal N)$ for some $X$-cactus $\mathcal N$ if and only if $\mathcal C$ is pairwise compatible (in the sense of strong compatibility of partitions, refined to respect the circular orders). If such an $\mathcal N$ exists it is unique up to isomorphism.
2. *(Poset.)* For $|X| \ge 2$, ordering isomorphism classes of $X$-cactuses by $\mathcal N_1 \le \mathcal N_2$ when $\mathcal N_1$ is obtained from $\mathcal N_2$ by contractions gives a graded poset whose unique minimum is the trivial $X$-cactus, whose coatom relations are single contractions, and whose maximal elements are the binary phylogenetic $X$-cactuses in which every internal vertex lies on a cycle. Moreover $\mathcal N \le \mathcal N'$ if and only if $\mathcal C(\mathcal N)$ is dominated by $\mathcal C(\mathcal N')$.
3. A least upper bound $\mathcal N$ of $X$-cactuses $\mathcal N_1, \dots, \mathcal N_m$, when it exists, satisfies $|\mathcal C(\mathcal N)| \le \big|\bigcup_{i} \mathcal C(\mathcal N_i)\big|$.

## Expansion

This is the cactus analogue of the splits-equivalence theorem: an $X$-tree is determined by its pairwise compatible splits. For partitions with more than two blocks, compatibility alone yields a semi-tree representation; the circular orders then pin down how each cycle is wired, and compatibility of the orders of two cycles guarantees they can be realized in the same cactus. The poset lets one compare cactuses by refinement, as for $X$-trees, and supports consensus constructions via upper and lower bounds.

## Sources

- Andrew Francis, Katharina T. Huber, Vincent Moulton and Taoyang Wu, "Encoding and ordering X-cactuses", Advances in Applied Mathematics 142 (2023), 102414, <https://doi.org/10.1016/j.aam.2022.102414>; numbering as in arXiv:2109.03183: Theorems 3.3, 4.1, 5.1 and 6.1.
