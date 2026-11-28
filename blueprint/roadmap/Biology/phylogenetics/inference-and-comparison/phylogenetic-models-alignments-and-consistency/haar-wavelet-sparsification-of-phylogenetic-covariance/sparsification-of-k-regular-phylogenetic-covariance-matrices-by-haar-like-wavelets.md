# Sparsification of $k$-regular phylogenetic covariance matrices by Haar-like wavelets

**Setting.** Let $T$ be a rooted tree with root $\circ$, leaf set $L$, internal nodes $I$ and edge lengths $\ell : E \to \mathbb R_+$; $T$ is $k$-regular if every non-root internal node has $k$ children (the root is planted), so $|L| = 1 + (k-1)(|I|-1)$. The **phylogenetic covariance matrix** is

$$C(i,j) = \sum_{e \in [i\wedge j,\,\circ]}\ell(e), \qquad i, j \in L,$$

the shared root-to-leaf branch length (the covariance of a Brownian trait on $T$). The **trace length** of an edge is $\ell^*(e) = |L(e)|\,\ell(e)$, with $L(e)$ the leaves below $e$, and $\ell^*(u,v) = \sum_{e\in[u,v]}\ell^*(e)$.

**Haar-like wavelets.** Let $\phi_\circ \equiv |L|^{-1/2}$. For an internal node $v \ne \circ$ with children $v_1, \dots, v_k$ and $1 \le n < k$, let $L_{v,n} = L(v_1) \cup \dots \cup L(v_n)$ and $L^+_{v,n} = L_{v,n} \cup L(v_{n+1})$, and set

$$\phi_{v,n} = \sqrt{\frac{|L(v_{n+1})|}{|L_{v,n}|\,|L^+_{v,n}|}}\,\mathbf 1_{L_{v,n}} - \sqrt{\frac{|L_{v,n}|}{|L(v_{n+1})|\,|L^+_{v,n}|}}\,\mathbf 1_{L(v_{n+1})}.$$

These $|L|$ functions form an orthonormal basis of $\mathbb R^L$; let $\Phi$ be the matrix with these columns.

**Theorem (diagonal action).** If $\psi$ is a Haar-like wavelet associated with $v \in I$, then $C\psi = \mathrm{diag}(\ell^*(L, v))\,\psi$, i.e. $(C\psi)(i) = \ell^*(i,v)\psi(i)$ for every leaf $i$.

**Theorem (sparsity bound).** Let $\zeta$ be the fraction of vanishing entries of $\Phi^\top C\Phi$ and $\mathrm{IPL}(T)$ the internal path length of $T$. Then

$$1 - \zeta \le \frac{(k-1)^2}{|I|} + 2(k-1)^2\frac{\mathrm{IPL}(T)}{|I|^2}.$$

In particular $\zeta = 1 - o(1)$ whenever $\mathrm{IPL}(T) \ll |I|^2$.

**Theorem (random trees).** For a uniformly random $k$-regular tree with $|I|$ internal nodes,

$$\mathbb E[\mathrm{IPL}(T)] = \sqrt{\frac{\pi k|I|^3}{2(k-1)}}\,\big(1 + O(|I|^{-1/2})\big), \qquad \mathbb V[\mathrm{IPL}(T)] = \frac{k}{2(k-1)}\Big(\frac{10}{3} - \pi\Big)|I|^3\big(1 + O(|I|^{-1/2})\big).$$

Hence $\mathrm{IPL}(T) = O_P(|I|^{3/2})$ and, for every $k \ge 2$, $\zeta \to 1$ in probability as $|I| \to \infty$.

## Proof sketch

A wavelet at $v$ is constant on the leaf sets of the children of $v$ and has mean zero, so in $C\psi$ all contributions from edges above $v$ cancel; only the branch lengths inside the clade of $v$ survive, weighted by subtree sizes, which is the trace length $\ell^*$. Consequently $\langle\phi', C\phi\rangle$ vanishes unless the supports of $\phi$ and $\phi'$ are nested along a root path, and the number of such pairs is controlled by the sum of depths of internal nodes, the internal path length. For random trees the generating function $Q(z)$ of $k$-regular trees satisfies $Q = 1 + zQ^k$-type equations with a square-root singularity at $z_k$, and singularity analysis gives the $|I|^{3/2}$ mean and $|I|^3$ variance. The covariance matrix can therefore be diagonalized up to a vanishing fraction of entries using two post-order traversals, without storing $C$.

## Sources

- S. P. Svihla, M. E. Lladser, "Sparsification of Phylogenetic Covariance Matrices of k-Regular Trees", in C. Mailler and S. Wild (eds.), *35th International Conference on Probabilistic, Combinatorial and Asymptotic Methods for the Analysis of Algorithms (AofA 2024)*, LIPIcs 302, Schloss Dagstuhl, 2024, 4:1–4:17, <https://doi.org/10.4230/LIPIcs.AofA.2024.4>. Preprint version: arXiv:2405.17847 (2024), Definition 2.1 and Theorem 2.1 (Section 2), Theorems 3.1–3.2 and Corollaries 3.1–3.3 (Section 3), <https://doi.org/10.48550/arXiv.2405.17847>.
