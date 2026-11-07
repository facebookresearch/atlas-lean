# Series of even powers of Fibonacci polynomials at even indices

Let $f_i$ be the
Fibonacci polynomials, defined by $f_0 = 0$, $f_1 = 1$ and $f_{i+2} = x f_{i+1} + f_i$. Let
$x > 0$ be real and let $k$ and $m$ be positive integers. If $k$ is odd, put $L = (k + 1)/2$ and
$s_r = 2r - 1$; if $k$ is even, put $L = k/2 + 1$ and $s_r = 2r$. Then

$$
\sum_{n \ge L} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{(k+1)j} f_{2k(m-j)}(x)
f_{4n(m-j)}(x)}{\bigl(f_{2n}(x)^2 - (-1)^k f_k(x)^2\bigr)^{2m}} =
(x^2 + 4)^{m-1} \sum_{r=1}^{k} \frac{1}{f_{s_r}(x)^{2m}}.
$$

## Sources

- Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article linzhou02172024, Theorem 1.1 (`fq-2024-linzhou02172024-thm-1.1`).
