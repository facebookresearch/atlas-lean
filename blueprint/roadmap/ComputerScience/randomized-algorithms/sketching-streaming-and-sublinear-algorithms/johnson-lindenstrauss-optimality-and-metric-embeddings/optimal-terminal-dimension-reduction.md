# Optimal terminal Johnson-Lindenstrauss embeddings

There is an absolute constant $C$ such that for every $0 < \varepsilon < 1$ and every finite $X \subset \mathbb{R}^d$ with $|X| = n > 1$ there is a map $f : \mathbb{R}^d \to \mathbb{R}^m$ with $m \le C\varepsilon^{-2}\log n$ such that

$$
\|x - y\|_2 \le \|f(x) - f(y)\|_2 \le (1 + \varepsilon)\|x - y\|_2 \quad \text{for all } x \in X \text{ and all } y \in \mathbb{R}^d .
$$

So distances from the terminals $X$ to every point of space are preserved with the same dimension bound $O(\varepsilon^{-2}\log n)$ as in the Johnson–Lindenstrauss lemma, improving the earlier terminal bound $O(\varepsilon^{-4}\log n)$; the map is necessarily nonlinear.

## Proof sketch

Start from a Johnson–Lindenstrauss map $\Pi$ of dimension $O(\varepsilon^{-2}\log n)$ that, in addition to preserving the norms of the differences $x - x'$, preserves inner products between normalized differences up to an additive $O(\varepsilon)$, a property of Gaussian matrices that holds with the same dimension by a sharper chaining analysis. For a non-terminal point $y$, let $x$ be its nearest terminal and set $f(y) = (\Pi x + u, \, c)$ with one extra coordinate $c$, where $u$ solves a small convex program enforcing the inner-product constraints with all terminals; feasibility of the program is shown by a von Neumann minimax argument together with the inner-product preservation of $\Pi$.

## Proof depends on

- [Distributional Johnson–Lindenstrauss lemma](../../probabilistic-analysis-tools/distributional-johnsonlindenstrauss-lemma.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- Shyam Narayanan, Jelani Nelson, "Optimal terminal dimensionality reduction in Euclidean space", STOC (2019), arXiv:1810.09250.
