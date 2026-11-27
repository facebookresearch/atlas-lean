# $S$ is positive definite iff no affine hyperplane contains all samples

Let $X$ be a real $n \times p$ data matrix whose rows $x_1, \dots, x_n$ are the samples. Its
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
$S$ is always
[positive semidefinite](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov-pos-semidef.md).
For every $n$, $S$ is positive definite ($w^\top S w > 0$ for every $w \ne 0$) exactly when no
affine hyperplane $\{x : x \cdot w = c\}$, $w \ne 0$, contains all the samples: for every
$w \in \mathbb{R}^p \setminus \{0\}$ and every $c \in \mathbb{R}$ some sample has
$x_i \cdot w \ne c$.

Since $\operatorname{rank} S \le \max(n - 1, 0)$, positive definiteness needs at least $p + 1$
samples when $p \ge 1$.
