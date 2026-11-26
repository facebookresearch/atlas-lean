# Spectral reconstruction of ultrametric trees from the ultrametric Laplacian

**Setting.** Let $(X, d, m)$ be a finite ultrametric space (the leaves of an ultrametric phylogenetic tree $T$ with $d$ the tree distance) with a positive measure $m$, and $k : [0,\infty) \to \mathbb{R}$ a kernel. Each internal node $n$ of $T$ corresponds to a ball $B_n \subseteq X$ with parent node $F(n)$. The *ultrametric Laplacian* is

$$L_Xu(x) = \sum_{y \in X} k\bigl(d(x,y)\bigr)\bigl(u(y) - u(x)\bigr)\,m(y).$$

**Hierarchical decomposition and spectrum.** If $k(\operatorname{diam}B_n) - k(\operatorname{diam}B_{F(n)}) > 0$ for every non-root internal node, then $L_X$ is a superposition of averaging operators on the balls with weights $a(B_n) = m(B_n)\bigl(k(\operatorname{diam}B_n) - k(\operatorname{diam}B_{F(n)})\bigr)$. Functions supported on a ball $B_n$, constant on each child ball and of zero $m$-mean, are eigenfunctions with eigenvalue

$$\lambda_n = -\sum_{y \in X\setminus B_n} k\bigl(d(x_0,y)\bigr)m(y) - k(\operatorname{diam}B_n)\,m(B_n), \qquad x_0 \in B_n,$$

with multiplicity (number of children of $n$) $-1$; together with the constants they span all functions on $X$.

**Theorem (spectral reconstruction).** For a labelled phylogenetic ultrametric tree with $m$ the counting (Lebesgue) measure, the decoration of internal nodes by eigenvalues and multiplicities of $L_X$ reconstructs the kernel values $k(\operatorname{diam}B_n)$, and hence the tree up to realization.

**Heat kernel and centrality.** If $m$ is a probability measure, $L_X$ generates an irreducible reversible continuous-time Markov chain with $P_t(x,y) = e^{tL_X}\delta_y(x) = H_t(x,y)\,m(y)$, whose unique stationary law is $m$. Its mean-first-passage centrality of leaf $i$ is an explicit sum over the balls containing $i$ of $-\lambda^{-1}$ times differences of inverse ball masses, giving a measure of evolutionary distinctiveness.

## Expansion

Ultrametricity means $k(d(x,y))$ is constant on each "annulus" $B_{F(n)} \setminus B_n$, so $L_X$ commutes with the projections onto ball averages and is diagonal in the associated Haar-type wavelet basis, as for the Vladimirov operator on $p$-adic balls. Each internal node contributes one eigenvalue, determined by the kernel on that node's diameter and above, so the eigenvalues read from the leaves up recover the kernel's values node by node; when $k$ is strictly monotone this recovers the node heights. The heat kernel is then an explicit spectral sum over the same basis.

## Sources

- Á. A. Morán Ledezma, "Spectral Geometry and Heat Kernels on Phylogenetic Trees" (2026), Section 3 operator, Propositions 3.3, 3.5 and 3.7, Theorem 3.10, Theorems 4.2 and 4.4, <https://doi.org/10.48550/arXiv.2603.20922>.
