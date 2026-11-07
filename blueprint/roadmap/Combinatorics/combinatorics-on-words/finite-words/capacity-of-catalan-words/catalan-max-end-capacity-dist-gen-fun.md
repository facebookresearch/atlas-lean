# Generating function for the capacity of Catalan words ending in their largest letter

For
natural numbers $n$ and $i$, let $b(n, i; q)$ be the capacity distribution of the Catalan words of
length $n$ that end in $i$ and have all letters at most $i$, viewed in $\mathbb{Z}[q, q^{-1}]$.
Let the formal power series $d_k(x; q)$ in $x$ over $\mathbb{Z}[q]$ be defined by $d_0 = 1$,
$d_1 = 1 - xq$, $d_2 = 1 - xq - xq^2$ and $d_k = (1 - xq^k)\, d_{k-1} - x^2 q^{2k-1} d_{k-3}$ for
$k \ge 3$. For a natural number $j$ and a power series $f(x; q)$ over $\mathbb{Z}[q]$ write
$f(q^j x; 1/q)$ for the series over $\mathbb{Z}[q, q^{-1}]$ whose coefficient of $x^n$ is
$q^{jn}$ times the coefficient of $x^n$ in $f$ with $q$ replaced by $q^{-1}$. For every natural
number $i \ge 1$, in formal power series in $x$ over $\mathbb{Z}[q, q^{-1}]$,

$$\sum_{n \ge 0} b(n, i; q)\, x^n = x^i \prod_{j=1}^{i} \Bigl(1 - x -
\frac{x}{d_{j-1}(q^j x; 1/q)} \sum_{m=1}^{j-1} x^{j-m} q^{j(j-m) + \binom{m}{2} - \binom{j}{2}}
d_{m-1}(q^j x; 1/q)\Bigr)^{-1}.$$

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 4 (`integers-2025-A5-lem-4`).
