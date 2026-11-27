# Fourth moments decay along expander walks

Let $G$ be a regular multigraph on a finite vertex set with walk operator $W$ and spectral expansion $\lambda = \lambda(G)$. For every $f : V \to \mathbb{R}$ with $\mathbb{E}_v f(v) = 0$ and all $s, t \ge 0$,

$$\mathbb{E}_v \bigl(W^{s+t} f\bigr)(v)^4 \le \bigl(\lambda^{4s} + \lambda^{2t}\bigr)\, \mathbb{E}_v f(v)^4, \qquad\text{in particular}\qquad \mathbb{E}_v (W^{2t} f)^4 \le 2\lambda^{2t}\, \mathbb{E}_v f^4.$$

Moreover $W$ never increases fourth moments. This is the $L^4$ contraction of a reversible Markov operator with a spectral gap, obtained without interpolation.

## Proof sketch

Jensen's inequality gives $(Wf)^2 \le W(f^2)$ pointwise. Put $g = W^s f$; then $(W^t g)^4 \le (W^t g^2)^2$, and $g^2$ is its mean $m = \mathbb{E} g^2 \le \lambda^{2s}\mathbb{E} f^2$ plus a mean-zero part whose second moment $W^t$ shrinks by $\lambda^{2t}$. Combining with $(\mathbb{E} f^2)^2 \le \mathbb{E} f^4$ gives the bound.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../../graph-families-and-operations/expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
