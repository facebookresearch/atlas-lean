# Orthonormal error contrasts rotate to diagonalize a symmetric matrix

Let $m$, $k$ and $r$ be finite index sets, $X$ a real $m \times k$ matrix, $K$ a real symmetric
$m \times m$ matrix and $A$ a real $r \times m$ matrix with $AX = 0$, $AA^\top = I$ and
$|r| + |k| = |m|$. Then there are a real $r \times r$ matrix $Q$ with $QQ^\top = Q^\top Q = I$ and
a vector $d \in \mathbb{R}^r$ such that $QA$ is an
[orthonormal error contrast diagonalizing $K$](is-spectral-contrast.md) with eigenvalues $d$:

$$QAX = 0, \qquad QA(QA)^\top = I, \qquad QAK(QA)^\top = \operatorname{diag}(d),$$

and $|r| + |k| = |m|$. If moreover $K$ is positive semidefinite, every $d_i \ge 0$. The $d_i$ are
the eigenvalues of $AKA^\top$.
