# Linear-time computation of the generalized Robinson-Foulds distance

**Lemma 3.** For rooted phylogenetic trees $T_1, T_2$ with $n = |L(T_1) \cup L(T_2)|$, the generalized Robinson-Foulds distance $GRF(T_1, T_2)$ can be computed in $O(n)$ time.

The key identity removes the quadratic double sums over clusters. Let $\delta_T(x)$ be the depth of leaf $x$, so that $x$ lies in exactly $\delta_T(x) + 1$ clusters of $T$, and let $\hat S(T) = \sum_{C \in \mathcal C(T)} |C| = \sum_{x \in L(T)} (\delta_T(x) + 1)$, a Sackin-type index. For any set of labels $X$, using $|C \oplus X| = |C| + |X| - 2|C \cap X|$,

$$\sum_{C \in \mathcal C(T)} |C \oplus X| = \hat S(T) + |\mathcal C(T)|\,|X| - 2 \sum_{x \in X \cap L(T)} (\delta_T(x) + 1),$$

and therefore

$$\sum_{x \in \mathcal C(T_1)} \sum_{y \in \mathcal C(T_2)} |x \oplus y| = |\mathcal C(T_2)|\,\hat S(T_1) + |\mathcal C(T_1)|\,\hat S(T_2) - 2 \sum_{i \in L(T_1) \cap L(T_2)} (\delta_{T_1}(i) + 1)(\delta_{T_2}(i) + 1).$$

The double sums in $GRF$ are this total minus the corresponding sums restricted to the common clusters $\mathcal C(T_1) \cap \mathcal C(T_2)$, which form the cluster set of a tree $H$ and are handled by the same identity with the depths in $H$.

## Depends on

- [Generalized Robinson-Foulds distance on trees with overlapping taxa](generalized-robinson-foulds-distance-on-trees-with-overlapping-taxa.md)

## Expansion

Postorder traversals give the depths and $\hat S(T_1), \hat S(T_2)$ in linear time, and Day's algorithm computes the cluster sets and their intersection $\mathcal C(T_1) \cap \mathcal C(T_2)$ in $O(n)$ time even with overlapping taxa. All remaining quantities are sums over leaves of products of depths, so the whole formula is evaluated in $O(n)$, matching the linear time of the classical Robinson-Foulds distance; direct evaluation of the definition would take $O(n^3)$ with sorted cluster lists or $O(n^2 \log n)$ with bit vectors.

## Sources

- M. Llabrés, F. Rosselló, G. Valiente, "The generalized Robinson-Foulds distance for phylogenetic trees", Journal of Computational Biology 28(12):1181-1195 (2021), Lemma 2, Corollary 1 and Lemma 3 (Section 3.3), <https://doi.org/10.1089/cmb.2021.0342>, PMCID PMC8742253.