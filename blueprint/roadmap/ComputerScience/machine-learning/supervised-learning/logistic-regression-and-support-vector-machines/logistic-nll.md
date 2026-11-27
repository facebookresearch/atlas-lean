# Negative log-likelihood of logistic regression

Let $X$ be a real $m \times \iota$ design matrix with rows $x_k$, and write $z = X\theta$ for the linear predictor. For labels $y \in \mathbb{R}^m$, the **logistic loss** is

$$\ell(\theta) = \sum_{k=1}^m \big(\log(1 + e^{z_k}) - y_k z_k\big).$$

An intercept is included by adding a constant column to $X$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §7.1.1 (the log-likelihood $l(a, b)$ of the logistic model (7.3)).
