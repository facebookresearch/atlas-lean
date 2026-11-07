# Even powers of Fibonacci polynomials at $n \pm k$

Let $f_i \in \mathbb{Z}[x]$ be the
Fibonacci polynomials, defined by $f_0 = 0$, $f_1 = 1$ and $f_{i+2} = x f_{i+1} + f_i$. For all
natural numbers $k \le n$ and every natural number $m$,

$$
(x^2 + 4)^{m-1} \bigl(f_{n+k}^{2m} - f_{n-k}^{2m}\bigr) =
\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(n+k+1)j} f_{2k(m-j)} f_{2n(m-j)}
$$

in $\mathbb{Z}[x]$, where for $m = 0$ the exponent $m - 1$ is read as $0$ (both sides are then
$0$).

## Sources

- Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article linzhou02172024, Lemma 3.1 (`fq-2024-linzhou02172024-lem-3.1`).
