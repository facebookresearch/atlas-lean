# Fibonacci numbers as binomially weighted sums

Let $F_k$ denote the $k$th Fibonacci
number. For every natural number $r \ge 1$ and every natural number $n$,

$$F_{n+2r} = \sum_{k=0}^{n} \binom{n + r - 1 - k}{r - 1} F_k +
\sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}$$

and

$$F_{n+2r} = \sum_{k=0}^{n} \binom{r + k - 1}{k} F_{n-k} +
\sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}.$$

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*, INTEGERS 24 (2024), Article A70, Corollary 1 (`integers-2024-A70-cor-1`).
