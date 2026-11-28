# Centring is multiplication by $I - n^{-1}\mathbf{1}\mathbf{1}^\top$

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with
[centred matrix](../principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$, where $\mathbf 1 \in \mathbb{R}^n$ is the all-ones vector. For
every $n$,

$$X_c = \Bigl(I_n - \frac1n \mathbf 1 \mathbf 1^\top\Bigr) X,$$

with the $n \times n$ centring matrix $I_n - \frac1n \mathbf 1 \mathbf 1^\top$. For $n = 0$ both
sides are the empty $0 \times p$ matrix.
