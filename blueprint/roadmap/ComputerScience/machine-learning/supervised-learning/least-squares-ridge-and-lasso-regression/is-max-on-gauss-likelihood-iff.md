# Least squares is maximum likelihood

Let $X$ be a real matrix with $m$ rows and columns
indexed by a finite set $\iota$, let $y \in \mathbb{R}^m$ and $v > 0$, and let $L$ be the Gaussian
likelihood of linear regression with noise variance $v$. Then $\theta_0 \in \mathbb{R}^\iota$
maximizes $L$ over $\mathbb{R}^\iota$ if and only if it solves the normal equations
$X^\top X \theta_0 = X^\top y$.
