# Logistic regression is a convex problem

Let $X$ be a real $m \times \iota$ design matrix with rows $x_k$, and write $z = X\theta$ for the linear predictor. For any labels $y \in \mathbb{R}^m$, the logistic loss $\theta \mapsto \sum_k \big(\log(1 + e^{z_k}) - y_k z_k\big)$ is convex on $\mathbb{R}^\iota$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §7.1.1 ("Since $l$ is a concave function of $a$ and $b$, the logistic regression problem can be solved as a convex optimization problem").
