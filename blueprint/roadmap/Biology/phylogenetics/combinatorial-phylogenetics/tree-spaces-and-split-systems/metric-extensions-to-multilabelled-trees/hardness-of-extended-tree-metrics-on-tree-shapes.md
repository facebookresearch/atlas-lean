# Hardness of extended tree metrics on multilabelled trees and tree shapes

**Metric extension.** A MUL-tree is a rooted tree whose leaves are labelled by a multiset $M$ of size $m$ over a set $X$; a phylogenetic tree is the case without repeated labels, and a *tree shape* the case where all labels coincide. Given a metric $d$ on phylogenetic trees, its extension to two MUL-trees $T_1, T_2$ with leaf multiset $M$ is

$$
d^*(T_1, T_2) = \min\ d(T_1^*, T_2^*),
$$

the minimum over all ways of bijectively relabelling the leaves by $\{1, \dots, m\}$ such that leaves of $T_1$ and of $T_2$ carrying the same element of $X$ receive the same subset of $\{1, \dots, m\}$; $d^*$ is a metric on MUL-trees. For tree shapes on $n$ leaves this is a minimum over all leaf labellings of both trees.

**Metrics.** The path-difference distance is $d_{path}(T_1, T_2) = \sum_{i,j} |\ell_{T_1}(i,j) - \ell_{T_2}(i,j)|$ with $\ell_T(i,j)$ the number of edges on the path from $i$ to $j$; the Robinson–Foulds distance $d_{RF}$ counts clusters present in exactly one tree.

**Theorem.**

1. Computing $d^*_{path}(T_1, T_2)$ for two tree shapes of the same size is NP-complete, even when both are binary.
2. Consequently, the quadratic assignment problem is NP-complete when the two matrices are the Robinson similarity matrix of one tree and the Robinson dissimilarity matrix of another.
3. Computing $d^*_{RF}(T_1, T_2)$ for two tree shapes of the same size is NP-complete, even if both have height at most $3$, and also when both are binary. For binary tree shapes of size $sz$,

$$
d^*_{RF}(T_1, T_2) = 4\,sz(T_1) - 2 - 2\mu(T_1, T_2),
$$

   where $\mu(T_1, T_2)$ is the size of a maximum *consistent cluster matching*: a set of vertex pairs $(v_1, v_2)$, $v_i \in V(T_i)$, whose subtrees have equal leaf counts, with $v_1, v_1'$ incomparable iff $v_2, v_2'$ are (so ancestry is preserved). For three tree shapes $|V(T_2)| + \mu(T_1, T_3) \ge \mu(T_1, T_2) + \mu(T_2, T_3)$.
4. Deciding $d^*_{RF}(T_1, T_2) \le k$ for tree shapes of size $n$ is fixed-parameter tractable in $k$, in time $O(2^{k \log(2k+1)} n^3)$.
5. Computing the size of a maximum agreement subtree of three unlabelled tree shapes is NP-complete.

Since tree shapes are special MUL-trees, the same hardness holds for the extensions of $d_{path}$ and $d_{RF}$ to arbitrary MUL-trees.

## Expansion

For $d_{path}$ hardness (in the strong sense) is by reduction from 3-Partition: one tree shape encodes the integers $a_i$ in subtree sizes, the other has $m$ parts of size $S = (\sum_i a_i)/m$, and a lower bound on $d^*_{path}$ is attained iff the $a_i$ split into groups of sum $S$. Because a leaf labelling of each tree just permutes the rows and columns of its path-length matrix, $d^*_{path}$ is an instance of quadratic assignment, which gives item 2. For $d_{RF}$, labelling both shapes so as to share as many clusters as possible is exactly a maximum consistent cluster matching, which yields the formula; hardness of computing $\mu$ comes from a reduction from Dominating Set, and the FPT algorithm is a bounded search tree over the at most $k$ clusters left unmatched. The agreement-subtree result reduces from Restricted 3D-Matching.

## Sources

- M. Lafond, N. El-Mabrouk, K. T. Huber, V. Moulton, "The complexity of comparing multiply-labelled trees by extending phylogenetic-tree metrics", arXiv:1803.05866 (2018): Section 1 (metric extension $d^*$), Section 3 (path-difference, Theorem 3.2), Section 4 (Theorem 4.1, quadratic assignment), Section 5 (consistent cluster matchings, Corollaries 5.3–5.4, Theorems 5.5, 5.6 and 5.9), Section 6 (Theorem 6.1, unlabelled MAST). <https://doi.org/10.48550/arXiv.1803.05866> Published version: Theoretical Computer Science 760 (2019) 15–34, <https://doi.org/10.1016/j.tcs.2018.08.006>.
