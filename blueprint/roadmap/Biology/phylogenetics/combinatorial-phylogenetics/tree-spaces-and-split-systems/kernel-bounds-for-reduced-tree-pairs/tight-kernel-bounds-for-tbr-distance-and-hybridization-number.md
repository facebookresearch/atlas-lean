# Tight kernel bounds for TBR distance and hybridization number under subtree and chain reductions

Let $T,T'$ be unrooted binary phylogenetic trees on a leaf set $X$, and let $d_{\mathrm{TBR}}(T,T')$ be their tree bisection and reconnection distance (the minimum number of TBR moves turning one into the other). It equals the unrooted hybridization number $h^u(T,T')=\min_N r(N)$, the minimum reticulation number of an unrooted binary phylogenetic network displaying both trees. Two data-reduction rules preserve $d_{\mathrm{TBR}}$:

- **subtree reduction**: replace a maximal pendant subtree with at least two leaves common to $T$ and $T'$ by a single new leaf;
- **chain reduction**: replace a maximal common $n$-chain of leaves with $n\ge4$ by a correctly oriented common $3$-chain.

**Theorem (TBR kernel).** If $d_{\mathrm{TBR}}(T,T')\ge2$ and $S,S'$ on $X'$ are obtained from $T,T'$ by exhaustive subtree and chain reductions, then

$$|X'| \le 15\,d_{\mathrm{TBR}}(T,T') - 9.$$

The bound is tight: for every $k\ge2$ there are subtree- and chain-reduced pairs with $d_{\mathrm{TBR}}=k$ and exactly $15k-9$ leaves. It remains tight for $k\ge4$ even when the common-cluster reduction is also applied, so smaller kernels need genuinely new reduction rules. This improves the earlier Allen-Steel bound $|X'|\le 28\,d_{\mathrm{TBR}}$.

**Theorem (rooted hybridization number).** Let $S,S'$ be rooted binary phylogenetic trees on $X$ with hybridization number $h(S,S')\ge1$.

1. If $S,S'$ are subtree and chain reduced, then $|X|\le 9h(S,S')-2$, and this bound is tight.
2. If in addition they are cluster reduced (no common non-trivial cluster), then $|X|\le 9h(S,S')-4$, and this bound is tight.

## Expansion

1. A minimum network displaying both trees with $k$ reticulations, after deleting leaves, is a subdivision of an *unrooted generator*: a cubic multigraph with $3(k-1)$ edges and $2(k-1)$ vertices.
2. In a reduced pair, each generator edge (side) can carry only a bounded number of pendant leaves, since longer common chains or pendant subtrees would have been reduced; the TBR counting gives at most $15k-9$ leaves, and the rooted analysis gives $9k-2$.
3. Tightness: explicit families $S_k,S'_k$ decorate every side of a generator to the maximum allowed while keeping the distance $k$; for cluster-reduced instances the root side cannot carry leaves, which removes two leaves in the rooted case.

## Sources

- S. Kelk, S. Linz, *A tight kernel for computing the tree bisection and reconnection distance between two phylogenetic trees*, arXiv:1811.06892 (Section 3 TBR kernel theorem, Section 4 tightness theorem and corollary, Section 5 rooted hybridization theorems). <https://doi.org/10.48550/arXiv.1811.06892> Published version: SIAM Journal on Discrete Mathematics, 33:1556-1574, 2019, <https://doi.org/10.1137/18M122724X>.
- B. L. Allen, M. Steel, Subtree transfer operations and their induced metrics on evolutionary trees, *Ann. Comb.* 5 (2001), 1–15. <https://doi.org/10.1007/s00026-001-8006-8>
