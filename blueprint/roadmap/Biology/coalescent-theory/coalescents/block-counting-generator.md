# Generator of the Λ-coalescent block-counting process

Let $\Lambda$ be a finite measure on $[0, 1]$ with [merger rates](merger-rate.md) $\lambda_{b,k}$ and [total merger rates](total-merger-rate.md) $\lambda_b$. For a natural number $n$, the block-counting generator is the $(n+1) \times (n+1)$ real matrix, with rows and columns indexed by the numbers of blocks $\{0, \dots, n\}$, whose entry in row $i$ and column $j$ is

- $-\lambda_i$ if $j = i$,
- $\binom{i}{i+1-j} \lambda_{i,\, i+1-j}$ if $j < i$ (a merger of $i + 1 - j$ blocks into one),
- $0$ if $j > i$.

Rows $0$ and $1$ are zero, so the states $0$ and $1$ are absorbing.
