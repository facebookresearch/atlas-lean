# Galled networks enumeration threshold

A phylogenetic network is **galled** if every reticulation lies in a tree cycle, i.e. a union of two edge-disjoint paths from a common tree node to a common reticulation, all of whose other nodes are tree nodes. Let $\mathrm{GN}_{n,k}$ be the number of galled networks with $n$ labeled leaves and $k$ reticulations, and $\mathrm{GTC}_{n,k}$ the number of galled tree-child networks.

**Theorem.** As $n \to \infty$ with $k = o(n^{1/2})$,

$$
\mathrm{GN}_{n,k} = \frac{2^{k-1}\sqrt2}{k!}\Big(\frac{2}{e}\Big)^n n^{n+2k-1}\Big(e^{-\sqrt{2k^3/n}} + o(1)\Big),
$$

and $\mathrm{GTC}_{n,k} \sim \frac{2^{k-1}\sqrt2}{k!}(2/e)^n n^{n+2k-1} e^{-\sqrt{2k^3/n}}$. Hence the first-order formula $\mathrm{GN}_{n,k} \sim \frac{2^{k-1}\sqrt2}{k!}(2/e)^n n^{n+2k-1}$, which coincides with the tree-child count, holds exactly in the range $k = o(n^{1/3})$. For $k/n^{1/3} \to \infty$ (still with $k = o(n^{1/2})$), the ratio of galled to tree-child networks tends to $0$.

## Depends on

- [Cube-root phase transition for semi-simplex tree-child networks](cube-root-phase-transition-for-semi-simplex-tree-child-networks.md)

## Expansion

The generating function of galled networks satisfies $G(z,v) = \sum_{j \ge 0} F_j(z)(vG(z,v))^j/j!$, where $F_j$ counts simplex tree-child structures with $j$ reticulations. Extracting the coefficient of $v^k$ by Lagrange inversion writes it as a sum over compositions $j_1 + \dots + j_s = k$. A combinatorial inequality, $\sum b_{j_1}\cdots b_{j_s} \le b_k (c_0/k)^{s-1} s!$, shows that the term with one block ($s = 1$) dominates uniformly for $k = o(n^{1/2})$. This gives $\mathrm{GTC}_{n,k} = \mathrm{SSTC}_{n,k}(1 + O(\sqrt{k/n}))$, so galled counts inherit the semi-simplex correction factor $e^{-\sqrt{2k^3/n}}$ from the semi-simplex count.

## Sources

- Michael Fuchs, Hao Yu, "A cube-root phase transition in tree-child networks and the enumeration threshold for galled networks", arXiv (2026). Definition 1.5, Theorem 1.6, Lemmas 3.1-3.4, Corollary 3.5. <https://doi.org/10.48550/arXiv.2608.20860>
