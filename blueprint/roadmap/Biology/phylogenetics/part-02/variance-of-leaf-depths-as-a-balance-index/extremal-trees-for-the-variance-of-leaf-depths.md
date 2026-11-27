# Extremal trees for the variance of leaf depths

**Definitions.** For a rooted tree $T$ with leaf set $L(T)$, $|L(T)| = n$, let $\delta_T(x)$ be the depth of leaf $x$ (number of edges from the root), $S(T) = \sum_x\delta_T(x)$ the Sackin index and $S^{(2)}(T) = \sum_x\delta_T(x)^2$. The **variance of the leaves' depths** is

$$V(T) = \frac1n S^{(2)}(T) - \frac{1}{n^2}S(T)^2.$$

The comb $K_n$ (caterpillar) has depths $1,2,\dots,n-1,n-1$. A bifurcating tree is **maximally balanced** ($B_n$) if at every internal node the descendant leaves split into two sets whose sizes differ by at most $1$.

**Theorem.**

1. Over all rooted trees with $n$ leaves (multifurcations allowed), the maximum of $V$ is attained exactly at the comb, with

    $$V(K_n) = \frac{(n-1)(n-2)(n^2 + 3n - 6)}{12n^2};$$

    the comb is bifurcating, so this is also the maximum among bifurcating trees.

2. The minimum over all rooted trees is $0$, attained exactly by trees whose leaves all have the same depth (e.g. the rooted star).
3. Among bifurcating trees, $B_n$ minimizes $V$ for every $n \le 183$, but not for $n = 184$: a tree with $174$ leaves of depth $8$, $9$ of depth $7$ and $1$ of depth $2$ has $V \approx 0.2379 < V(B_{184}) \approx 0.2382$.
4. As $m\to\infty$, the fraction of $n \in [2, 2^m]$ for which $V(B_n)$ is minimal among bifurcating trees with $n$ leaves tends to $0$. Minimizers belong to explicit families of trees, which yields an $O(n\log n)$ algorithm for the minimum.

## Expansion

The comb result is proved by induction on $n$, tracking how $V$ changes when a deepest leaf is removed. The intuition for part 3 is that $V$ depends only on the multiset of depths; the trees depth-equivalent to $B_n$, which have leaves on at most two consecutive levels and minimize the Sackin index, minimize the spread only while $n$ is close to a power of $2$. Far from powers of $2$, putting almost all leaves on one level and paying for a single very shallow leaf reduces the variance below that of the two-level configuration. So $V$ agrees with Sackin, Colless and cophenetic indices on the most imbalanced tree but not on the most balanced one.

## Sources

- T. M. Coronado, A. Mir, F. Rosselló, L. Rotger, "On Sackin's original proposal: the variance of the leaves' depths as a phylogenetic balance index", BMC Bioinformatics 21 (2020) 154, Results, Eq (3), Example 1, Theorems 1–3, Fig. 2 and Algorithm 1, <https://doi.org/10.1186/s12859-020-3405-1>, PMCID PMC7181513.
