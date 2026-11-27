# The hinge loss bounds the number of misclassified examples

For every $w$ and $b$, the number of examples $k$ with $y_k(x_k^{\mathsf T} w + b) \le 0$ (misclassified or on the decision boundary) is at most the total hinge loss $\sum_k \max(0, 1 - y_k(x_k^{\mathsf T} w + b))$, since each such term is at least $1$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §8.6.1 (the slack sum "is a convex relaxation for the number of misclassified points").
