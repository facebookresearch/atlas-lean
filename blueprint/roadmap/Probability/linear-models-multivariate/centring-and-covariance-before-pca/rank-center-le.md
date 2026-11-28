# Centred data matrix has rank at most $n - 1$

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with
[centred matrix](../principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$. Then

$$\operatorname{rank} X_c \le n - 1,$$

where $n - 1$ is truncated subtraction, $0$ for $n = 0$ (a matrix with no rows has rank $0$). For
$n \ge 1$ the bound holds because $\mathbf 1^\top X_c = 0$: the all-ones vector
$\mathbf 1 \in \mathbb{R}^n$ lies in the left kernel of $X_c$.
