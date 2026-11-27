# Solutions of the ridge normal equations minimize the ridge objective

Let $X$ be a real
matrix with $m$ rows and columns indexed by a finite set $\iota$, let $y \in \mathbb{R}^m$ and
$\lambda \ge 0$, and write $\|\cdot\|$ for the Euclidean norm. If $\theta_0 \in \mathbb{R}^\iota$
satisfies $(X^\top X + \lambda I)\theta_0 = X^\top y$, then for every $\theta \in \mathbb{R}^\iota$,
$\|y - X\theta_0\|^2 + \lambda \|\theta_0\|^2 \le \|y - X\theta\|^2 + \lambda \|\theta\|^2$.
