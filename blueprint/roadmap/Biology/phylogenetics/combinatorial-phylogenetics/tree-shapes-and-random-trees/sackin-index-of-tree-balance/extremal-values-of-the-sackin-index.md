# Extremal values of the Sackin index

**Setting.** For a rooted tree $T$ with leaf set $V^1(T)$ and inner vertices $\mathring{V}(T)$ (no vertex of in- and out-degree one, except possibly the root), the **Sackin index** is

$$\mathcal{S}(T) = \sum_{u \in \mathring{V}(T)} n_u = \sum_{x \in V^1(T)} \delta_x,$$

where $n_u$ is the number of leaves below $u$ and $\delta_x$ is the depth of leaf $x$; the two sums agree (Lemma 1). Let $T_n^{cat}$ be the caterpillar and $T_n^{star}$ the star on $n$ leaves, and write $k = \lceil \log_2 n \rceil$. For binary $T$, $\mathcal{S}(T) = i(T) + 2(n-1)$ with $i(T)$ the total internal path length (Lemma 2).

**Theorem.**
1. (Maximum, binary) Among rooted binary trees with $n$ leaves, $T_n^{cat}$ is the unique maximizer of $\mathcal{S}$, with $\mathcal{S}(T_n^{cat}) = \frac{n(n+1)}{2} - 1$. It remains the unique maximizer among all rooted (not necessarily binary) trees.
2. (Minimum, binary) A rooted binary tree $T$ with $n$ leaves minimizes $\mathcal{S}$ if and only if $T$ is the fully balanced tree $T_k^{fb}$ (when $n = 2^k$) or all leaves of $T$ have depth $k-1$ or $k$ (when $n < 2^k$). The minimum value is

$$\min_T \mathcal{S}(T) = n(k+1) - 2^k,$$

which equals $k\,2^k$ for $n = 2^k$; the sequence of minima starting at $n=1$ is $0,2,5,8,12,16,20,24,\ldots$ (OEIS A003314; a one-leaf tree has no inner vertex, although the source's Remark 4 lists $1$ for $n=1$)
3. (Minimum, arbitrary) For $n \ge 2$, the star $T_n^{star}$ is the unique rooted tree minimizing $\mathcal{S}$, with $\mathcal{S}(T_n^{star}) = n$.

## Expansion

The maximum follows by a leaf-moving argument: detaching a cherry and reattaching it at the deepest leaf never decreases leaf depths, so only the caterpillar, whose leaf depths are $1,2,\ldots,n-1,n-1$, is maximal. For the minimum, if two leaves differ in depth by at least two, moving a cherry from the deeper position to the shallower leaf strictly lowers the sum of depths, so a minimizer uses at most two consecutive depths; a binary tree with $n$ leaves at depths $k-1$ and $k$ has $2^k - n$ leaves at depth $k-1$ and $2n - 2^k$ at depth $k$, which gives $n(k+1) - 2^k$. In the non-binary case, contracting any inner edge lowers the depth of every leaf below it, so only the star survives. Larger $\mathcal{S}$ means a less balanced tree, which is why the index is used to test the Yule and other tree-shape null models in phylogenetics.

## Sources

- Mareike Fischer, "Extremal values of the Sackin tree balance index", arXiv:1801.10418 (2018), Section 3, Definitions 1–3, Lemmas 1–2, Theorems 1, 2, 4 and 5, Remark 4, <https://doi.org/10.48550/arXiv.1801.10418>. Published version: Annals of Combinatorics 25 (2021) 515–541, <https://doi.org/10.1007/s00026-021-00539-2>.
