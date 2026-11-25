# Convexity of the lasso objective

Let $X$ be a real matrix with $m$ rows and columns
indexed by a finite set $\iota$, let $y \in \mathbb{R}^m$ and let $\lambda \ge 0$. Then the lasso
objective $\theta \mapsto \sum_k (y_k - (X\theta)_k)^2 + \lambda \sum_{i \in \iota} |\theta_i|$
is a convex function on all of $\mathbb{R}^\iota$.
