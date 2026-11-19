# Closed form of ridge regression

Let $X$ be a real matrix with $m$ rows and columns indexed
by a finite set $\iota$, let $y \in \mathbb{R}^m$ and $\lambda > 0$, and write $\|\cdot\|$ for the
Euclidean norm. The ridge estimate $\hat\theta = (X^\top X + \lambda I)^{-1} X^\top y$ minimizes
the ridge objective: for every $\theta \in \mathbb{R}^\iota$,
$\|y - X\hat\theta\|^2 + \lambda \|\hat\theta\|^2 \le \|y - X\theta\|^2 + \lambda \|\theta\|^2$.
