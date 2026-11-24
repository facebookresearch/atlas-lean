# Partitions in a diagonal class with more parts than the initial staircase

Let $\alpha$
be a partition of $n$ with diagonal sequence $\delta(\alpha) = (d_j)_{j \ge 1}$, set $d_0 = 0$,
and let $q, L \ge 0$ be integers with $d_j = j$ for all $1 \le j \le q$, $d_{q+1} \ne q + 1$,
$d_L \ne 0$ and $d_{L+1} = 0$. Put $b_i = \max(d_i - d_{i+1}, 0)$. Then for every $k > q$ the
number of partitions of $n$ with exactly $k$ parts whose diagonal sequence equals
$\delta(\alpha)$ is

$$\binom{b_{k-1} + b_k}{b_{k-1} + 1} \prod_{i=q}^{k-2} \binom{b_i + b_{i+1} + 1}{b_i + 1}
\prod_{i=k}^{L-1} \binom{b_i + b_{i+1}}{b_i}.$$

For $k > L$ both sides are $0$.

## Sources

- Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*, INTEGERS 25 (2025), Article A60, Proposition 9.
