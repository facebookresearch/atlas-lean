# Barak et al.: nearly tight SoS lower bound for planted clique via pseudocalibration

There is a constant $c > 0$ such that for every $d = d(n)$, with high probability over $G \sim G(n, 1/2)$, the degree-$d$ sum-of-squares relaxation for the clique number satisfies

$$
\mathrm{SoS}_d(G) \ge n^{1/2 - c\sqrt{d/\log n}}.
$$

In particular, for every $d = o(\log n)$, degree-$d$ SoS cannot distinguish $G(n,1/2)$ from a graph with a planted clique of size $n^{1/2 - o(1)}$, which is nearly tight since degree $2$ succeeds at $O(\sqrt{n})$.

## Proof sketch

Define the pseudo-expectation by pseudocalibration with respect to the planted clique distribution with clique size $k = n^{1/2 - \varepsilon}$ and truncation $\tau \approx d/\varepsilon$. Its value and linear constraints follow from the planted distribution. Positivity of the moment matrix is the main step: decompose it into graph matrices, factor it approximately as $LQL^{\top}$ through minimum vertex separators, and use the graph-matrix norm bounds to show that the error terms are dominated by the positive diagonal part.

## Depends on

- [The degree-d SoS relaxation of the clique number](planted-clique-sos-value.md)

## Proof depends on

- [Graph matrices and their norm bounds](graph-matrices.md)
- [Pseudocalibration of pseudo-expectations](pseudocalibration.md)
- [Juhász / Feige–Krauthgamer: degree-2 SoS fails for cliques of size o(sqrt n)](theta-random-graph.md)

## Sources

- B. Barak, S. B. Hopkins, J. Kelner, P. K. Kothari, A. Moitra, A. Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", FOCS (2016); SIAM Journal on Computing 48 (2019), arXiv:1604.03084.
- R. Meka, A. Potechin, A. Wigderson, "Sum-of-squares lower bounds for planted clique", STOC (2015), arXiv:1503.06447.
- Y. Deshpande, A. Montanari, "Improved sum-of-squares lower bounds for hidden clique and hidden submatrix problems", COLT (2015), arXiv:1502.06590.
