# The set of least-squares minimizers

Let $X$ be a real matrix with $m$ rows and columns indexed by a finite set $\iota$, let $y \in \mathbb{R}^m$, and let $S(\theta) = \|y - X\theta\|^2$ be the residual sum of squares, with the Euclidean norm. Let $\theta_0$ be any solution of the normal equations $X^\top X\theta_0 = X^\top y$, which exists. Then:

1. **The minimizers form an affine subspace.** $\{\theta : S(\theta) \le S(\theta') \text{ for all } \theta'\} = \theta_0 + \ker X$.
2. **Uniqueness exactly for injective $X$.** The minimizer is unique if and only if $X$ has trivial kernel, that is, has linearly independent columns; then it is $(X^\top X)^{-1} X^\top y$.
3. **Fitted values are unique.** Every minimizer gives the same fitted vector $X\theta = X\theta_0$, the orthogonal projection of $y$ onto the column space of $X$.

The statement allows rank-deficient $X$, including zero columns or rows; no inverse is used unless $X$ is injective.

**Proof.** By the normal-equation characterization, $\theta$ is a minimizer if and only if $X^\top X \theta = X^\top y$, that is, $X^\top X(\theta - \theta_0) = 0$. Since $v^\top X^\top X v = \|Xv\|^2$, $\ker X^\top X = \ker X$, which gives part 1. Part 2 follows from part 1, and when $\ker X = 0$ the Gram matrix $X^\top X$ is invertible. For part 3, $X(\theta - \theta_0) = 0$ for every minimizer; the residual $y - X\theta_0$ satisfies $X^\top(y - X\theta_0) = 0$, so it is orthogonal to the column space and $X\theta_0$ is the orthogonal projection.

## Proof depends on

- [Least squares and the normal equations](rss-le-iff-normal.md): minimizers are exactly the solutions of the normal equations
- [Least-squares estimates exist](exists-normal.md): the normal equations always have a solution

## Sources

- S. Boyd and L. Vandenberghe, *Introduction to Applied Linear Algebra: Vectors, Matrices, and Least Squares*, Cambridge University Press, 2018, <https://web.stanford.edu/~boyd/vmls/vmls.pdf>, Section 12.2 (pp. 227–230): under the assumption that the columns of $A$ are linearly independent, the normal equations $A^\top A x = A^\top b$, their unique solution $\hat x = (A^\top A)^{-1}A^\top b$, and the orthogonality principle (12.9). The rank-deficient minimizer set is derived on the page.
