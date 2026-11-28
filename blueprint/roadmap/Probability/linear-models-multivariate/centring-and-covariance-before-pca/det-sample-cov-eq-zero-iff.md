# Sample covariance is singular iff samples lie in an affine hyperplane

Let $X$ be a real $n \times p$ data matrix whose rows $x_1, \dots, x_n$ are the samples, with
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
$S$. For every $n$, $S$ is singular, $\det S = 0$, exactly when all samples lie in one affine
hyperplane: there are $w \in \mathbb{R}^p$ with $w \ne 0$ and $c \in \mathbb{R}$ such that
$x_i \cdot w = c$ for every $i$.

By contrast, $\det(X^\top X) = 0$ exactly when all samples lie in a hyperplane through the origin.
The two can differ: the samples $(1, 0)$ and $(0, 1)$ of $\mathbb{R}^2$ lie on the line
$\{x : x \cdot (1, 1) = 1\}$, so $S$ is singular, while $X^\top X$ is the identity matrix.
