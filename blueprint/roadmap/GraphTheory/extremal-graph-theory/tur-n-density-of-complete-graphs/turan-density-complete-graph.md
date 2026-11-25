# Turán density of complete graphs

For $r \ge 1$, the Turán density of the complete graph on $r + 1$ vertices is

$$\pi(K_{r+1}) = 1 - \frac{1}{r}:$$

graphs on $n$ vertices without $K_{r+1}$ have at most $(1 - 1/r + o(1))\binom{n}{2}$ edges, and the Turán graphs attain it. For $r = 2$ this is Mantel's density $\pi(K_3) = 1/2$, and for $r = 1$ it says that $\pi(K_2) = 0$.

The proof squeezes $t(n, r)/\binom{n}{2}$ between the upper bound $2r\, t(n, r) \le (r - 1)n^2$ and the [lower bound](turan-number-lower-bound.md) $2r\, t(n, r) \ge (r - 1)(n^2 - r^2)$, where $t(n, r)$, the number of edges of the Turán graph $T(n, r)$, is the extremal number of $K_{r+1}$ by Turán's theorem.

## Sources

- P. Turán, On an extremal problem in graph theory (in Hungarian), Mat. Fiz. Lapok 48 (1941), 436-452.
