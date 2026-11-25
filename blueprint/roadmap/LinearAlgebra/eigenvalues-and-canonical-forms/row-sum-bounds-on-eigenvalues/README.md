# Spectral radius under a row-sum bound

Let $K$ be a real square matrix indexed by a finite nonempty set, with nonnegative entries and all row sums at most $1$: $\sum_j K_{ij} \le 1$ for every $i$. Then every complex eigenvalue $\lambda$ of $K$ satisfies $|\lambda| \le 1$: the spectral radius of $K$ is at most $1$.

## Idea

If $Kx = \lambda x$ and $i$ is an index where $|x_i|$ is largest, then $|\lambda|\,|x_i| = |\sum_j K_{ij} x_j| \le \sum_j K_{ij} |x_i| \le |x_i|$, so $|\lambda| \le 1$. Equivalently, the spectral radius is at most the operator norm for the maximum norm, which is the largest absolute row sum. Row-stochastic matrices, such as transition matrices of Markov chains, satisfy the hypothesis with equality. If $K$ is moreover positive semidefinite, its eigenvalues are real and lie in $[0, 1]$.

## Statements

- [Spectral radius under a row-sum bound](spectral-radius-le-one-of-row-sum-le-one.md)
- [Eigenvalues under a row-sum bound](eigenvalues-mem-icc-zero-one-of-row-sum.md): for a positive semidefinite matrix, the eigenvalues lie in $[0, 1]$
