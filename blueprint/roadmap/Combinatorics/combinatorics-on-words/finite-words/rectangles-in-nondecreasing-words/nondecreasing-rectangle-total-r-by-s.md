# Generating function for $r \times s$ rectangles in nondecreasing words

Let $k \ge 1$,
$r \ge 1$ and $s \ge 1$, let $g_k(n)$ be the total number of $r \times s$ rectangles over all
nondecreasing words of length $n$ over $[k] = \{1, \dots, k\}$, and let $m = \max(k + 1 - r, 0)$.
Then, as formal power series over $\mathbb{Z}$,

$$
\Big(\sum_{n \ge 0} g_k(n)\, x^n\Big) (1 - x)^{k+1} =
x^s \sum_{0 \le i \le k+1-r} (-1)^i \binom{i+s-2}{i} \binom{m+s}{s+i+1} x^i,
$$

where the sum is empty when $r \ge k + 2$, and for every $n \ge s$,

$$
g_k(n) = \sum_{i=0}^{\min(m,\, n-s)} (-1)^i \binom{i+s-2}{i} \binom{m+s}{s+i+1}
\binom{n-s-i+k}{k}.
$$

For $s = 1$ the factor $\binom{i+s-2}{i} = \binom{i-1}{i}$ is $1$ at $i = 0$ and $0$ for $i \ge 1$.

## Sources

- Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and Smirnov Words*, Journal of Integer Sequences 27 (2024), Article 24.8.4, Corollary 6 (`jis-2024-24.8.4-cor-6`).
