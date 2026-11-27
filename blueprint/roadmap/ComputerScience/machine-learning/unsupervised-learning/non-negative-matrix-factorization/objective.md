# Objective of nonnegative matrix factorization

Let $m, n, k$ be finite index sets. The NMF objective of $X \in \mathbb{R}^{m \times n}$,
$W \in \mathbb{R}^{m \times k}$ and $H \in \mathbb{R}^{k \times n}$ is the squared Frobenius
distance $\|X - W H\|_F^2 = \sum_{i, j} (X_{ij} - (W H)_{ij})^2$ between the data $X$ and the
product $W H$.
