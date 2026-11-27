# Order-dependent distances along cherry-picking sequences

**Cherry-picking sequences.** For rooted binary phylogenetic $X$-trees $T, T'$ with $|X| = n$, a sequence $S = (x_1, \dots, x_n)$ of the elements of $X$ is a **cherry-picking sequence** for $T$ if each $x_i$, $i \le n-1$, is a leaf of a cherry of $T|(X \setminus \{x_1, \dots, x_{i-1}\})$; it is **common** if it is one for both trees. The element $x_i$ ($i < n$) **agrees** if its cherry $\{x_i, y\}$ is a cherry of both restricted trees, and the **weight** $wt(S)$ is the number of $x_i$, $i \le n-1$, that disagree. The ordering **induced** by $S$ is $\sigma(x_i) = n - i + 1$. The minimum weight $s(T, T')$ of a common cherry-picking sequence equals the temporal tree-child hybridization number $h_t(T, T')$: the minimum number of reticulations in a temporal tree-child network displaying both trees.

**Vector distances.** $d^\sigma_{\mathrm{OLA}}$ and $d^\sigma_{\mathrm{P2V}}$ are the Hamming distances between the ordered-leaf-attachment and Phylo2Vec vectors of $T$ and $T'$ under $\sigma$, and $d^\sigma_{\mathrm{HOP}}$ is the longest-common-subsequence distance between their HOP vectors, as defined in [HOP measure equals the hybridization number](hop-measure-equals-the-hybridization-number.md) and [OLA measure is bounded by the rSPR distance](ola-measure-is-bounded-by-the-rspr-distance.md). (Phylo2Vec grows the tree in the same order as OLA but relabels the internal vertices after each attachment, cherry by cherry, with $i+1, \dots, 2i-1$.)

**Statement.**

1. If $S$ is a common cherry-picking sequence for $T$ and $T'$ and $\sigma$ is the ordering it induces, then

$$d^\sigma_{\mathrm{OLA}}(T, T') = d^\sigma_{\mathrm{HOP}}(T, T') = d^\sigma_{\mathrm{P2V}}(T, T') = wt(S).$$

2. Writing $d^{\mathrm{CPS}}_\Theta(T, T')$ for the minimum of $d^\sigma_\Theta(T, T')$ over orderings induced by common cherry-picking sequences, for $\Theta \in \{\mathrm{OLA}, \mathrm{HOP}, \mathrm{P2V}\}$,

$$d^{\mathrm{CPS}}_{\mathrm{OLA}}(T, T') = d^{\mathrm{CPS}}_{\mathrm{HOP}}(T, T') = d^{\mathrm{CPS}}_{\mathrm{P2V}}(T, T') = h_t(T, T').$$

In general $d^{\mathrm{CPS}}_\Theta$ can exceed the unrestricted minimum $d^*_\Theta$.

## Depends on

- [HOP measure equals the hybridization number](hop-measure-equals-the-hybridization-number.md)
- [OLA measure is bounded by the rSPR distance](ola-measure-is-bounded-by-the-rspr-distance.md)

## Expansion

Under an induced ordering, each newly attached leaf is placed beside a leaf to form a cherry, so every entry of the OLA vector is a leaf rank rather than an internal label, and the OLA and Phylo2Vec vectors of a single tree coincide. Coordinate $\sigma(x_i)$ of the two OLA vectors differs exactly when $x_i$ disagrees, so the Hamming distance is $wt(S)$; an analogous path-by-path comparison of HOP blocks gives the same count. Part 2 follows by minimizing over common sequences and the identity $s(T, T') = h_t(T, T')$.

## Sources

- S. Linz, K. St. John, C. Semple and K. Wicke, "Order-dependent dissimilarity measures on phylogenetic trees", *Journal of Mathematical Biology* 92(4) (2026), 53, Theorem 6, Theorem 7, Lemmas 8 and 9, Corollaries 2 and 3, <https://doi.org/10.1007/s00285-026-02373-7> (preprint arXiv:2507.11254).
