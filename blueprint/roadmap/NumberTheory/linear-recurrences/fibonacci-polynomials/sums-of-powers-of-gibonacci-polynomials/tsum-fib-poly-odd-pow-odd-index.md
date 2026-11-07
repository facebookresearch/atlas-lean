# Odd-power series over odd-indexed Fibonacci polynomials

Let $x > 0$ be real, let $f_n$
and $\ell_n$ denote the Fibonacci and Lucas polynomials evaluated at $x$, given by $f_0 = 0$,
$f_1 = 1$, $\ell_0 = 2$, $\ell_1 = x$ and the recurrence $z_{n+2} = x z_{n+1} + z_n$ for both, and
let $k$ be a positive integer and $m$ a natural number. Put $M = (k + 1)/2$ if $k$ is odd and
$M = k/2$ if $k$ is even. If $k$ is odd, then

$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^j f_{(2(n+M)+1)(2m+1-2j)}
\ell_{k(2m+1-2j)}}{\left(f_{2(n+M)+1}^2 - f_k^2\right)^{2m+1}} =
(x^2 + 4)^m \sum_{r=1}^{k} \frac{1}{f_{2r}^{2m+1}},$$

and if $k$ is even, then

$$\sum_{n=0}^{\infty} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} \ell_{(2(n+M)+1)(2m+1-2j)}
f_{k(2m+1-2j)}}{\left(f_{2(n+M)+1}^2 + f_k^2\right)^{2m+1}} =
(x^2 + 4)^m \sum_{r=1}^{k} \frac{1}{f_{2r-1}^{2m+1}}.$$

These are the source's sums over $n \ge M$ with the summation index shifted to start at $0$.

## Sources

- Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article linzhou02172024, Theorem 1.7.
