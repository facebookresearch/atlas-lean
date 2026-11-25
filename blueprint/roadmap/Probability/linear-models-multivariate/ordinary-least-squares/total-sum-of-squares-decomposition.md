# Decomposition of the total sum of squares

Let $n \ge 1$ and let $X$ be a real $n \times p$ matrix whose column space contains the constant vector $\mathbf 1$, let $\hat y$ be the least-squares fitted vector of $y$ and $e = y - \hat y$. Then $\sum_i (y_i - \bar y)^2 = \sum_i (\hat y_i - \bar y)^2 + \sum_i e_i^2$, since $\hat y - \bar y\mathbf 1$ lies in the column space and $e$ is orthogonal to it. This holds whether or not $X$ has full rank. If $y$ is not constant, $R^2 = 1 - \sum_i e_i^2/\sum_i (y_i - \bar y)^2$ is defined and lies in $[0, 1]$. Without the constant vector the identity can fail: for $n = 2$, $X = (1, 0)^{\mathsf T}$ and $y = (0, 1)$, the fitted vector is $0$, and $\tfrac12 \ne \tfrac12 + 1$.

## Proof depends on

- [Least-squares fitted values are the orthogonal projection onto the column space](fitted-values-are-the-orthogonal-projection.md): the fitted vector is the orthogonal projection, so the residual is orthogonal to the column space.

## Sources

- G. Rodríguez, *Generalized Linear Models*, chapter 2 "Linear models for continuous data", Princeton University, <https://grodri.github.io/glms/notes/c2.pdf>, §2.4.4 (coefficient of determination)
