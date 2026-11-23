# The logistic loss is the negative log-likelihood of the logistic model

Let $X$ be a real $m \times \iota$ design matrix with rows $x_k$, and write $z = X\theta$ for the linear predictor. With $p_k = \sigma(z_k) = e^{z_k}/(1 + e^{z_k})$,

$$\ell(\theta) = -\sum_{k=1}^m \big(y_k \log p_k + (1 - y_k) \log(1 - p_k)\big).$$

For labels $y_k \in \{0, 1\}$ the right side is minus the log-likelihood of the observed labels under the logistic model $P(y_k = 1) = p_k$, so minimizing $\ell$ is maximum likelihood estimation.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §7.1.1, eq. (7.3) and the log-likelihood derived from it.
