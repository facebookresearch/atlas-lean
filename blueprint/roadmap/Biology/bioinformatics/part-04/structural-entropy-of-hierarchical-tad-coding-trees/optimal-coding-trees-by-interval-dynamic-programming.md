# Optimal coding trees by interval dynamic programming

**Definitions.** Let $X = (x_{ij})_{1\le i,j\le n}$ be a symmetric nonnegative Hi-C matrix on bins $b_1,\dots,b_n$ with zero diagonal, and $2m = \sum_{i,j} x_{ij}$. A coding tree $T$ is a rooted tree whose root $\lambda_T$ codes all bins, each node $u$ codes a set $b_T(u)$ of consecutive bins, and the children of a node partition its bins. For a set $U$ of bins let $V(U) = \sum_{i\in U}\sum_{j} x_{ij}$ (volume) and $g(U) = \sum_{i\in U}\sum_{j\notin U} x_{ij}$ (cut). The structural entropy of a non-root node $u$ with parent $p(u)$, and of a bin $b_i$ lying in leaf $e(i)$, are

$$S_T(X;u) = -\frac{g(u)}{2m}\log_2\frac{V(u)}{V(p(u))},\qquad S_T(X;b_i) = -\frac{g(b_i)}{2m}\log_2\frac{V(b_i)}{V(e(i))},$$

and the entropy of the tree is $S_T(X) = \sum_{u\in T} S_T(X;u) + \sum_{i=1}^n S_T(X;b_i)$ (the root contributes $0$). If $v_1,\dots,v_\ell$ partition the bins of $v$ then $\sum_i g(v_i) \ge g(v)$ and $\sum_i V(v_i) \ge V(v)$.

**Lemma (monotonicity in leaves).** The minimum structural entropy over coding trees with $k+1$ leaves is at most the minimum over trees with $k$ leaves.

**Lemma (binarization).** For every matrix there is a binary coding tree of minimum structural entropy: replacing the children $c_1,\dots,c_\ell$ ($\ell \ge 3$) of a node $v$ by $c_1$ and a new node $u$ with children $c_2,\dots,c_\ell$ changes the entropy by

$$S_{T_a}(X) - S_{T_b}(X) = \frac{g(u) - \sum_{i\ge 2} g(c_i)}{2m}\,\log_2\frac{V(u)}{V(v)} \ \ge 0.$$

**Theorem.**

1. Let $S(i{:}j,k)$ be the minimum entropy of a binary coding tree on bins $b_i,\dots,b_j$ with $k$ leaves, and $H_l(i_l{:}i_r,j)$, $H_r(i_l{:}i_r,j)$ the entropies of the left child $b_{i_l..j}$ and right child $b_{j+1..i_r}$ of a node coding $b_{i_l..i_r}$. Then

    $$S(1{:}n,k) = \min_{1\le i<n,\ 1\le k_1<k}\Big[S(1{:}i,k_1) + S(i+1{:}n,k-k_1) + H_l(1{:}n,i) + H_r(1{:}n,i)\Big],$$

    and an optimal coding tree with $k$ leaves is computed in $O(k^2 n^3)$ time.

2. Restricting to (not necessarily binary) coding trees of height at most $h$ with at most $k$ leaves, an optimal tree is computed exactly by an analogous interval recurrence in $O(n^4 k^2 h)$ time.

## Expansion

Splitting a leaf $v$ into consecutive children $v_1, v_2$ adds the nonpositive-log terms of the two new nodes but lowers each bin's term because the bin now sits in a smaller leaf; the net change is $\sum_{s=1,2}\frac{g(v_s) - \sum_{i\in v_s} g(b_i)}{2m}\log_2\frac{V(v_s)}{V(v)} \ge 0$ since the cut inequality makes the numerators nonpositive and the logarithms are nonpositive. Hence entropy alone always prefers more leaves, and $k$ (or $h$) must be fixed or chosen by a separate criterion. Binarization lets the search range over binary trees, and because every node codes an interval of bins, the optimal subtrees on the two sides of a split are independent, which gives the recurrence. The $O(n^3)$ child-entropy terms are precomputed in constant time each, and each of the $O(kn^2)$ table entries takes $O(kn)$ time.

## Sources

- Y. W. Zhang, M. B. Wang, S. C. Li, "SuperTAD: robust detection of hierarchical topologically associated domains with optimized structural information", Genome Biology 22:45 (2021), Methods, Eqs (1)–(6), Lemmas 1–3 and Theorems 1–2, <https://doi.org/10.1186/s13059-020-02234-6>, PMCID PMC7831269.
