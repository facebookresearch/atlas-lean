# Hadamard bound for zero-one determinants

Let $n \ge 1$ and let $B$ be an $n \times n$ real matrix each of whose entries is $0$ or $1$. Then

$$|\det B| \le 2^{-n} (n + 1)^{(n+1)/2}.$$

## Idea

Matrices with entries in $\{0, 1\}$ and matrices with entries $\pm 1$ are related by a classical trick: bordering $2B$ with a row and a column and subtracting gives an $(n+1) \times (n+1)$ matrix with entries $\pm 1$ and determinant $\pm 2^n \det B$. Hadamard's inequality bounds the latter by $(n+1)^{(n+1)/2}$. The bound is attained exactly when a Hadamard matrix of order $n + 1$ exists, so the maximal determinant problem for $0$–$1$ matrices of order $n$ is equivalent to that for $\pm 1$ matrices of order $n + 1$.

## Statements

- [Hadamard bound for zero-one determinants](hadamard-zero-one-determinant-bound.md)
