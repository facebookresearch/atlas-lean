# Generating function for $1 \times s$ rectangles in nondecreasing words

Let $k \ge 1$ and
$s \ge 1$, and let $f_k(n)$ be the total number of $1 \times s$ rectangles over all nondecreasing
words of length $n$ over $[k] = \{1, \dots, k\}$. Then, as formal power series over $\mathbb{Z}$,

$$
\Big(\sum_{n \ge 0} f_k(n)\, x^n\Big) (1 - x)^{k+1} =
x^s \sum_{i=0}^{k-1} (-1)^i \binom{i+s-2}{i} \binom{k+s}{s+i+1} x^i,
$$

and for every $n \ge s$,

$$
f_k(n) = \sum_{i=0}^{\min(k-1,\, n-s)} (-1)^i \binom{i+s-2}{i} \binom{k+s}{s+i+1}
\binom{n-s-i+k}{k}.
$$

For $s = 1$ the factor $\binom{i+s-2}{i} = \binom{i-1}{i}$ is $1$ at $i = 0$ and $0$ for $i \ge 1$.

## Sources

- Sela Fried and Toufik Mansour, *Counting Rectangles of Size r × s in Nondecreasing and Smirnov Words*, Journal of Integer Sequences 27 (2024), Article 24.8.4, Corollary 2 (`jis-2024-24.8.4-cor-2`).
