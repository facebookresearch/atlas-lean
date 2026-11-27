# Generalized Robinson-Foulds distance on trees with overlapping taxa

Let $T_1, T_2$ be rooted phylogenetic trees whose leaf sets $L(T_1), L(T_2)$ may differ (overlapping taxa), and let $\mathcal C(T)$ be the set of clusters (descendant leaf sets of nodes) of $T$; a phylogenetic tree is determined by $\mathcal C(T)$. Write $x \oplus y$ for symmetric difference and $U = |\mathcal C(T_1) \cup \mathcal C(T_2)|$. The (normalized) Robinson-Foulds distance is $RF(T_1, T_2) = |\mathcal C(T_1) \oplus \mathcal C(T_2)| / U$, and the **generalized Robinson-Foulds distance** is

$$GRF(T_1, T_2) = \sum_{x \in \mathcal C(T_1)} \sum_{y \in \mathcal C(T_2) \setminus \mathcal C(T_1)} \frac{|x \oplus y|}{U\,|\mathcal C(T_1)|} \;+\; \sum_{x \in \mathcal C(T_1) \setminus \mathcal C(T_2)} \sum_{y \in \mathcal C(T_2)} \frac{|x \oplus y|}{U\,|\mathcal C(T_2)|}.$$

**Metric.** $GRF$ is a metric on rooted phylogenetic trees over arbitrary finite label sets: $GRF(T_1, T_2) = 0$ iff $T_1 = T_2$, it is symmetric, and it satisfies the triangle inequality. Unlike $RF$, it does not become trivial for trees with overlapping taxa, whose clusters mostly differ, because nearly equal clusters contribute small amounts.

**Lemma 1.** (a) For trees on the same taxa, $RF(T_1, T_2) \le GRF(T_1, T_2)$. (b) There is no constant $C$ with $GRF(T_1, T_2) \le C \cdot RF(T_1, T_2)$ for all pairs of trees on a common taxon set: for the caterpillar $K_n$ and the tree $K_n(2)$ obtained by contracting the arc from its root to its internal child,

$$GRF(K_n, K_n(2)) = \frac{3(n^2 - 3n + 4)}{4(2n-1)(n-1)}, \qquad RF(K_n, K_n(2)) = \frac{1}{2n-1},$$

whose ratio $\tfrac{3(n^2 - 3n + 4)}{4(n-1)}$ is unbounded. So $GRF$ and $RF$ are equivalent on each fixed taxon set but not uniformly in the number of leaves.

The resolution of $RF$ on binary trees with $n$ labelled leaves is $n - 1$ distinct values; $GRF$ takes many more ($\Theta(n^2)$ values in the authors' exhaustive and sampled experiments).

## Depends on

- [Robinson-Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

The metric property follows from Fujita's construction of a metric on finite sets of sets from a metric on sets, applied to $|x \oplus y|$, together with the fact that trees are determined by their clusters. For (a), every term with $x \ne y$ has $|x \oplus y| \ge 1$, and the inner sums have $|\mathcal C(T_1)|$ and $|\mathcal C(T_2)|$ terms respectively, so $GRF \ge (|\mathcal C(T_2) \setminus \mathcal C(T_1)| + |\mathcal C(T_1) \setminus \mathcal C(T_2)|)/U = RF$. For (b), $K_n$ and $K_n(2)$ differ in the single cluster $\{2, \dots, n\}$, which is far, in symmetric difference, from most other clusters of $K_n$, so $GRF$ stays bounded away from 0 while $RF$ is $1/(2n-1)$.

## Sources

- M. Llabrés, F. Rosselló, G. Valiente, "The generalized Robinson-Foulds distance for phylogenetic trees", Journal of Computational Biology 28(12):1181-1195 (2021), Definition 1, Example 1 and Lemma 1, <https://doi.org/10.1089/cmb.2021.0342>, PMCID PMC8742253.