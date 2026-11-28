# Low-degree hardness of planted clique below the square root

Let $\mathbb{Q}_n = G(n, 1/2)$ and let $\mathbb{P}_n$ be $G(n,1/2)$ with a clique planted on a uniformly random set of $k$ vertices (the planted clique model), or on the set obtained by putting each vertex in it independently with probability $k/n$. If $k \le n^{1/2 - \epsilon}$ for a constant $\epsilon > 0$, then for every constant $C > 0$, $\|L_n^{\le D}\| = O(1)$ for all degrees $D \le C \log n$ (Hopkins, Lemma 2.4.1, proved for independent inclusion; for a uniformly random $k$-set each Fourier coefficient is $(k)_v/(n)_v \le (k/n)^v$, with $(m)_v = m(m-1)\cdots(m-v+1)$ and $v$ the number of vertices the edge set spans, so the same bound follows), whereas the edge count, a degree-one statistic, succeeds once $k/\sqrt{n} \to \infty$, and spectral methods succeed for $k \ge C\sqrt{n}$ with $C$ a large enough constant.

## Proof sketch

In the $\pm 1$ basis of edge indicators, $L_n$ has Fourier coefficients $\mathbb{E}_S[\chi_\alpha]$ supported on edge sets $\alpha$ spanned by the planted set, with $\mathbb{E}[\chi_\alpha] = (k/n)^{|V(\alpha)|}$ under independent inclusion (at most this for a uniformly random $k$-set); summing over edge sets of size at most $D$ grouped by their vertex sets bounds $\|L^{\le D}\|^2 - 1$ by a sum over vertex counts $v \le 2D$ of $n^{v}(k/n)^{2v}$ times the number of edge sets with $v$ vertices and at most $D$ edges, which stays bounded when $k^2/n \le n^{-2\epsilon}$ and $D \le C \log n$.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)
- [Planted clique model, search and detection problems](../../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)

## Proof depends on

- [Second moment method: bounded likelihood ratio norm rules out detection](likelihood-ratio-second-moment-method.md)
- [Low-degree advantage for planted problems over the hypercube](boolean-low-degree-advantage.md)

## Sources

- S. B. Hopkins, "Statistical Inference and the Sum of Squares Method", PhD thesis, Cornell University (2018).
- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A Nearly Tight Sum-of-Squares Lower Bound for the Planted Clique Problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
