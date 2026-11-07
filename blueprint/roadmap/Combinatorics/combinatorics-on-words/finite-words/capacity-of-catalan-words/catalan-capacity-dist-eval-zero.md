# Zero-capacity Catalan words with a given last letter

For $2 \le i \le n$, let
$a(n, i; q)$ be the capacity distribution of the Catalan words of length $n$ ending in $i$, so that
$a(n, i; 0)$ is the number of those words with capacity $0$. Then

$$
a(n, i; 0) = \sum_{m=0}^{n-i} \binom{n-m-2}{i-2} F_{2m-1},
$$

where $F_k$ is the $k$-th Fibonacci number ($F_1 = F_2 = 1$) and $F_{-1} = 1$.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Theorem 3 (`integers-2025-A5-thm-3`).
