# The support vector machine is a convex problem

For $\lambda \ge 0$, the soft-margin SVM objective $J(w, b) = \sum_k \max(0, 1 - y_k(x_k^{\mathsf T} w + b)) + \lambda\, w^{\mathsf T} w$ is jointly convex in $(w, b)$.

## Sources

- T. Hastie, R. Tibshirani and J. Friedman, *The Elements of Statistical Learning*, 2nd ed., Springer, 2009, §12.3.2.
- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §8.6.1.
