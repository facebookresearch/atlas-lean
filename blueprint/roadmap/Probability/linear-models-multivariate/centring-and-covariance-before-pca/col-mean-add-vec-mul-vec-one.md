# With $n \ge 1$ samples, a shift by $c$ shifts the column means by $c$

Let $X$ be a real $n \times p$ data matrix whose rows are $n \ge 1$ samples, with column means
$\bar x$
([sample means](../../../Probability/linear-models-multivariate/principal-component-analysis/col-mean.md)),
let $c \in \mathbb{R}^p$ and let $\mathbf 1 \in \mathbb{R}^n$ be the all-ones vector. Adding $c$ to
every sample adds $c$ to the column means: the column means of $X + \mathbf 1 c^\top$ are
$\bar x + c$.

The hypothesis $n \ge 1$ is needed: for $n = 0$ all column means are $0$ by convention, so the
identity fails whenever $c \ne 0$.
