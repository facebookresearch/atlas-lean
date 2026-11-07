# Even-power series over odd-indexed Fibonacci polynomials

Let $x > 0$ be real, let $f_n$
denote the Fibonacci polynomials evaluated at $x$, given by $f_0 = 0$, $f_1 = 1$ and
$f_{n+2} = x f_{n+1} + f_n$, and let $k$ and $m$ be positive integers. Put $M = (k + 1)/2$ and
$t_r = 2r$ if $k$ is odd, and $M = k/2$ and $t_r = 2r - 1$ if $k$ is even. Then

$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{kj} f_{2k(m-j)}
f_{(4(n+M)+2)(m-j)}}{\left(f_{2(n+M)+1}^2 + (-1)^k f_k^2\right)^{2m}} =
(x^2 + 4)^{m-1} \sum_{r=1}^{k} \frac{1}{f_{t_r}^{2m}}.$$

This is the source's sum over $n \ge M$ with the summation index shifted to start at $0$.

## Sources

- Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article linzhou02172024, Theorem 1.3 (`fq-2024-linzhou02172024-thm-1.3`).
