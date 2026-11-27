# A nearest-neighbour interchange changes an induced partition tree exactly when all four flanks are represented

Let $T$ be an unrooted binary tree on $X$, let $e$ be an internal edge of $T$ and let $e_1, e_2, e_3, e_4$ be the four edges adjacent to $e$, with $A, B, C, D$ the species sets of the four subtrees hanging from them, so $X = A \sqcup B \sqcup C \sqcup D$ and $e = (A \cup B) \mid (C \cup D)$. Let $T_{\mathrm{NNI}}$ be either tree obtained from $T$ by a nearest-neighbour interchange around $e$, and let $Y \subseteq X$ be a partition species set with [edge map](induced-partition-tree-edge-map.md) $f$.

**Theorem.** The topologies of $T|_{Y}$ and $T_{\mathrm{NNI}}|_{Y}$ differ if and only if

$$A \cap Y \neq \emptyset,\quad B \cap Y \neq \emptyset,\quad C \cap Y \neq \emptyset,\quad D \cap Y \neq \emptyset,$$

equivalently if and only if $f(e_1), f(e_2), f(e_3), f(e_4)$ are all different from $\epsilon$. When the condition holds, $T_{\mathrm{NNI}}|_{Y}$ is obtained from $T|_{Y}$ by the corresponding interchange of the images (swapping $f(e_1)$ with $f(e_3)$ when $e_1$ and $e_3$ are swapped on $T$). When it fails, $T_{\mathrm{NNI}}|_{Y} = T|_{Y}$ as topologies, so $T$ and $T_{\mathrm{NNI}}$ lie on one partial terrace; if it fails for every partition they lie on one full terrace. This topological criterion holds whatever the edge-length model. Under the edge-unlinked partition model, an unchanged induced topology also leaves the optimal partition score unchanged, so on a full terrace no partitioned score needs recomputation; under edge-linked models the induced edge lengths can change without a topology change, and the scores need not be equal.

## Depends on

- [Induced partition tree and the edge map of a supermatrix](induced-partition-tree-edge-map.md)

## Proof depends on

- [Clusters determine an unrooted binary tree](../../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/iso-of-cluster-set-eq.md)
- [Post-order recursion for the edge map](edge-map-recursion.md)

## Proof sketch

An interchange around $e$ replaces the split $(A \cup B) \mid (C \cup D)$ by $(A \cup C) \mid (B \cup D)$ or $(A \cup D) \mid (B \cup C)$ and leaves every other split of $T$ unchanged. A tree on a leaf set is determined by its set of splits, so $T|_Y$ and $T_{\mathrm{NNI}}|_Y$ differ precisely when the restriction to $Y$ of the old and new central splits differ and both are nontrivial. If one of the four intersections is empty, say $D \cap Y = \emptyset$, then $(A \cup B) \cap Y \mid (C \cup D) \cap Y$ and $(A \cup D) \cap Y \mid (B \cup C) \cap Y$ are splits of $Y$ obtained from the same three-block partition of $Y$, and all restricted split systems agree, so the induced topologies coincide. If all four are nonempty, the two restricted central splits are distinct nontrivial splits of $Y$, so the induced topologies differ. Since the recursion recomputes only the map of the modified split, $F$ is updated in $O(k)$ time after an interchange, which is negligible beside a likelihood evaluation; under the edge-unlinked partition model no re-optimization at all is needed for the unchanged partitions. Analogous criteria, with the same proof pattern, hold for subtree pruning and regrafting and for tree bisection and reconnection.

## Sources

- O. Chernomor, A. von Haeseler and B. Q. Minh, "Terrace aware data structure for phylogenomic inference from supermatrices", Systematic Biology 65 (2016), 997–1008, conditions (C.1) and (C.2) and Appendix 3, <https://doi.org/10.1093/sysbio/syw037>, PMCID: PMC5066062.
- O. Chernomor, B. Q. Minh and A. von Haeseler, "Consequences of common topological rearrangements for partition trees in phylogenomic inference", Journal of Computational Biology 22 (2015), 1129–1142, Propositions 1–3.
