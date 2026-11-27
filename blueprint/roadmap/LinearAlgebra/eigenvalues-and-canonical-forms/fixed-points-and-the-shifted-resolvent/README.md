# Fixed point and shifted resolvent

Let $K$ be a real positive semidefinite $n \times n$ matrix, let $\lambda > 0$ and let $Y \in \mathbb{R}^n$.
A vector $z \in \mathbb{R}^n$ satisfies the fixed-point equation $z = \lambda K (Y - z)$ if and only if
it solves $(I + \lambda K) z = \lambda K Y$, if and only if $z = (\lambda^{-1} I + K)^{-1} K Y$; moreover
$(\lambda^{-1} I + K)^{-1} K = K (K + \lambda^{-1} I)^{-1}$.

## Idea

The fixed-point equation is linear in $z$: collecting the terms in $z$ gives
$(I + \lambda K) z = \lambda K Y$, and $I + \lambda K = \lambda(\lambda^{-1} I + K)$ is invertible because
the eigenvalues of $K$ are nonnegative. With the eigenvalue bound for matrices with row sums at most
$1$, this controls a smoothing step: if $K$ also has nonnegative entries and row sums at most $1$, the
eigenvalues of $(\lambda^{-1} I + K)^{-1} K$ are $\lambda t / (1 + \lambda t)$ for the eigenvalues
$t \in [0, 1]$ of $K$, so the solution satisfies $\|z\|_2 \le \frac{\lambda}{1 + \lambda} \|Y\|_2$.

## Statements

- [Fixed point and shifted resolvent](fixed-point-iff-shifted-resolvent.md)

## Background

- [Spectral radius under a row-sum bound](../row-sum-bounds-on-eigenvalues/README.md): the eigenvalue bound used for the smoothing step
