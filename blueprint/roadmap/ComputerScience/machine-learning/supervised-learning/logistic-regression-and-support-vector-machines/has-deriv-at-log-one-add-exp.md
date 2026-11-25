# Derivative of the softplus function

For every $t \in \mathbb{R}$, the softplus function $s \mapsto \log(1 + e^s)$ is differentiable at $t$ with derivative the sigmoid $\sigma(t) = 1/(1 + e^{-t}) = e^t/(1 + e^t)$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §7.1.1, eq. (7.3) (the logistic function).
