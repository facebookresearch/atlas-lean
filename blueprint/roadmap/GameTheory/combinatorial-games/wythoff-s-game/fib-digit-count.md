# Fibonacci digit count

Let $F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$. For
$n, s, k_0 \in \mathbb{N}$, the digit count of $n$ searched from $k_0$ in at most $s$ steps is
the least $k$ with $k_0 \le k < k_0 + s$ and $n < F_k$ if there is one, and $k_0 + s$
otherwise.

With $k_0 = 0$ and $s = n + 1$ it is the number of digits of the greedy Fibonacci
representation of $n$, the least $k$ with $n < F_k$, which exists since $n < F_n$.

## Sources

- Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026), Article 26.1.6, Definition `def:fib_rep` (greedy representation).
