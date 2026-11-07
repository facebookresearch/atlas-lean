# Iterated convolution of Fibonacci $m$-step and $(m+p)$-step numbers

Let $F^{(k)}_j$ be
the $j$-th Fibonacci $k$-step number: the sequence starts $F^{(k)}_0 = 0$, $F^{(k)}_1 = 1$, and each
later term is the sum of the $k$ terms before it (terms of negative index being $0$). For all
natural numbers $m$, $p$ and $n$ with $m \ge 1$ and $n \ge m$,

$$\sum_{k=0}^{p-1} \sum_{j=0}^{n-m-k} F^{(m)}_j \, F^{(m+p)}_{n-m-k-j} =
F^{(m+p)}_n - F^{(m)}_n,$$

where an inner sum whose upper limit $n - m - k$ is negative counts as $0$.

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 3.
