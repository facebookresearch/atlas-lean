# Low-degree and sum-of-squares hardness of planted clique below the square root

Let $\mathbb{Q}_n = G(n, 1/2)$ and $\mathbb{P}_n$ be $G(n,1/2)$ with a clique planted on a uniformly random set of $k$ vertices. If $k \le n^{1/2 - \epsilon}$ for a constant $\epsilon > 0$, then $\|L_n^{\le D}\| = O(1)$ for all degrees $D \le c_\epsilon \log^2 n$, whereas for $k \ge C\sqrt{n\log n}$ simple degree-one statistics (the edge count) and for $k \ge c\sqrt{n}$ spectral methods succeed. Moreover, with high probability over $G \sim G(n,1/2)$, the degree-$d$ sum-of-squares relaxation of the maximum clique has value at least $n^{1/2 - c\sqrt{d/\log n}}$, so degree-$o(\log n)$ sum-of-squares cannot certify the absence of cliques of size $n^{1/2 - o(1)}$.

## Proof sketch

In the $\pm 1$ basis of edge indicators, $L_n$ has Fourier coefficients $\mathbb{E}_S[\chi_\alpha]$ supported on edge sets $\alpha$ spanned by the planted set, with $\mathbb{E}[\chi_\alpha] = (k/n)^{|V(\alpha)|}$; summing over edge sets of size at most $D$ grouped by their vertex sets bounds $\|L^{\le D}\|^2 - 1$ by a sum over vertex counts $v \le 2D$ of $n^{v}(k/n)^{2v}$ times the number of edge sets with $v$ vertices and at most $D$ edges, which stays bounded when $k^2/n \le n^{-2\epsilon}$ and $D$ is polylogarithmic. The sum-of-squares bound uses pseudo-calibration: define pseudo-moments as the low-degree projection of the planted posterior moments and prove positivity of the resulting moment matrix via graph-matrix norm bounds.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)
- [The degree-d SoS relaxation of the clique number](../../../Logic/proof-theory/sum-of-squares-lower-bounds-and-pseudocalibration/planted-clique-sos-value.md)

## Proof depends on

- [Second moment method: bounded likelihood ratio norm rules out detection](likelihood-ratio-second-moment-method.md)
- [Low-degree advantage for planted problems over the hypercube](boolean-low-degree-advantage.md)
- [Pseudo-calibration for sum-of-squares lower bounds](../../high-dimensional-probability/statistical-query-lower-bounds-for-planted-problems/pseudo-calibration.md)
- [Graph matrices and their norm bounds](../../../Logic/proof-theory/sum-of-squares-lower-bounds-and-pseudocalibration/graph-matrices.md)

## Sources

- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).
- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A Nearly Tight Sum-of-Squares Lower Bound for the Planted Clique Problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
