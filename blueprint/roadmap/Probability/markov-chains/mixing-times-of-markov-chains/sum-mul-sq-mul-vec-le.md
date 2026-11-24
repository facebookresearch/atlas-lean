# A reversible stochastic matrix is a contraction of $L^2(\pi)$

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$ with $\pi(x) \ge 0$ for every $x$, and $K$ a
stochastic $S \times S$ matrix (nonnegative entries, rows summing to $1$) in detailed balance with
$\pi$: $\pi(x) K(x, y) = \pi(y) K(y, x)$ for all $x, y$. Then for every $g : S \to \mathbb{R}$,

$$\sum_{x \in S} \pi(x)\, (Kg)(x)^2 \le \sum_{x \in S} \pi(x)\, g(x)^2, \qquad (Kg)(x) = \sum_{y \in S} K(x, y)\, g(y) .$$

Each $(Kg)(x)^2$ is at most $\sum_y K(x, y)\, g(y)^2$ by Jensen's inequality, and detailed balance
makes $\pi$ stationary.
