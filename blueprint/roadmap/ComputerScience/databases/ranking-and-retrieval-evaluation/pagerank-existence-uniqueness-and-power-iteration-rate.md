# PageRank existence, uniqueness and power-iteration rate

Let $G = \alpha P + (1 - \alpha) v \mathbf{1}^{\mathsf T}$ be a Google matrix on $n \ge 1$ nodes, with $P$ column-stochastic, $v$ a probability vector and $0 < \alpha < 1$.
For probability vectors $x$ and $y$, $\lVert G x - G y \rVert_1 \le \alpha \lVert x - y \rVert_1$. Hence $G$ has a unique stationary probability vector $\pi$, and power
iteration from any probability vector $x_0$ satisfies $\lVert G^k x_0 - \pi \rVert_1 \le \alpha^k \lVert x_0 - \pi \rVert_1$. The contraction holds on differences of probability
vectors (more generally on vectors with coordinate sum zero), not on all vectors.

## Proof

If $\mathbf{1}^{\mathsf T} z = 0$ then $G z = \alpha P z + (1-\alpha) v (\mathbf{1}^{\mathsf T} z) = \alpha P z$, and $\lVert P z \rVert_1 \le \sum_j \lvert z_j \rvert \sum_i P_{ij} = \lVert z \rVert_1$
for a column-stochastic $P$; apply this to $z = x - y$. $G$ maps the probability simplex $\Delta$ into itself, since its entries are nonnegative and $\mathbf{1}^{\mathsf T} G = \mathbf{1}^{\mathsf T}$.
*Uniqueness:* if $\pi, \pi' \in \Delta$ are fixed by $G$, then $\lVert \pi - \pi' \rVert_1 = \lVert G\pi - G\pi' \rVert_1 \le \alpha \lVert \pi - \pi' \rVert_1$, so $\pi = \pi'$.
*Existence:* for $x_0 \in \Delta$ and $x_k = G^k x_0$, $\lVert x_{k+1} - x_k \rVert_1 \le \alpha^k \lVert x_1 - x_0 \rVert_1$, so $\lVert x_l - x_k \rVert_1 \le \alpha^k \lVert x_1 - x_0 \rVert_1/(1 - \alpha)$
for $l \ge k$ and $(x_k)$ is a Cauchy sequence in $\mathbb{R}^n$. Its limit $\pi$ lies in the closed set $\Delta$, and $G\pi = \pi$ by continuity of $G$.
*Rate:* $\lVert G^k x_0 - \pi \rVert_1 = \lVert G^k x_0 - G^k \pi \rVert_1 \le \alpha^k \lVert x_0 - \pi \rVert_1$ by $k$ applications of the contraction bound.

## Depends on

- [Google matrix](google-matrix.md)

## Sources

- D. F. Gleich, *PageRank beyond the Web*, SIAM Review 57(3) (2015), 321–363; arXiv:1407.5107, pp. 2–3: existence and uniqueness of the solution of $(I - \alpha P)x = (1-\alpha)v$ (the paragraph after Definition 2.1), the error recursion $x - x^{(k+1)} = \alpha P (x - x^{(k)})$, and Theorem 2.2 ($\lVert x - x^{(k)} \rVert_1 \le \alpha^k \lVert x - v \rVert_1$ from $x^{(0)} = v$); a general probability vector $x_0$ follows from the same recursion. <https://arxiv.org/abs/1407.5107>
- A. N. Langville and C. D. Meyer, *Deeper inside PageRank*, Internet Mathematics 1(3) (2004), 335–380, Theorem 5.1 (the spectrum of $\alpha \bar P + (1-\alpha) e v^{\mathsf T}$ is $\{1, \alpha\lambda_2, \dots, \alpha\lambda_n\}$, the spectral, asymptotic rate of the power method).
