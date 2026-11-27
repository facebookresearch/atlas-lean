# Optimal terminal Johnson-Lindenstrauss embeddings

There is an absolute constant $C$ such that for every $0 < \varepsilon < 1$ and every finite $X \subset \mathbb{R}^d$ with $|X| = n > 1$ there is a map $f : \mathbb{R}^d \to \mathbb{R}^m$ with $m \le C\varepsilon^{-2}\log n$ such that

$$
\|x - y\|_2 \le \|f(x) - f(y)\|_2 \le (1 + \varepsilon)\|x - y\|_2 \quad \text{for all } x \in X \text{ and all } y \in \mathbb{R}^d .
$$

So distances from the terminals $X$ to every point of space are preserved with the same dimension bound $O(\varepsilon^{-2}\log n)$ as in the Johnson–Lindenstrauss lemma, improving the earlier terminal bound $O(\varepsilon^{-4}\log n)$. When $m < d$ the map is necessarily nonlinear (indeed not affine): a linear or affine map into fewer dimensions has a nonzero direction $v$ with $f(x + v) = f(x)$, which violates the lower bound for a terminal $x$ and $y = x + v$. When $C\varepsilon^{-2}\log n \ge d$ the identity map already works.

## Proof sketch

Start from a random matrix $\Pi$ with subgaussian entries and $O(\varepsilon^{-2}\log n)$ rows that provides *$\varepsilon$-convex hull distortion* for the set $T$ of normalized differences $(x - x')/\|x - x'\|_2$ of terminals: $|\|\Pi z\|_2 - \|z\|_2| \le \varepsilon$ for every $z$ in the convex hull of $T$, which holds with high probability by a chaining (Gaussian width) argument. For a non-terminal point $y$, let $x$ be its nearest terminal and set $f(y) = (\Pi x + u, \, c)$ with one extra coordinate $c$, where $u$ solves a small convex program enforcing the inner-product constraints with all terminals; feasibility of the program is shown by a von Neumann minimax argument together with the convex hull distortion of $\Pi$. This is a sharper analysis of an outer-extension construction of Mahabadi, Makarychev, Makarychev and Razenshteyn, whose earlier analysis needed dimension $O(\varepsilon^{-4}\log n)$.

## Proof depends on

- [Distributional Johnson–Lindenstrauss lemma](../../probabilistic-analysis-tools/distributional-johnsonlindenstrauss-lemma.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- Shyam Narayanan, Jelani Nelson, "Optimal terminal dimensionality reduction in Euclidean space", STOC (2019), arXiv:1810.09250.
