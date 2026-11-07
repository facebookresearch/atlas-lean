# Odd-power sums with odd-index Lucas polynomial denominators

Let $f_n$ and $\ell_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, \ell\}$, evaluated at a real number
$x > 0$, let $k$ be a positive integer and $m$ a natural number, and put $M = (k + 1)/2$ if $k$ is
odd and $M = k/2$ if $k$ is even. If $k$ is odd, then

$$\sum_{n \ge M} \frac{\sum_{j=0}^{m} \binom{2m+1}{j} \ell_{(2n+1)(2m+1-2j)} \ell_{k(2m+1-2j)}}
{\left(\ell_{2n+1}^2 + (x^2 + 4) f_k^2\right)^{2m+1}}
= \sum_{r=1}^{k} \frac{1}{\ell_{2r}^{2m+1}},$$

and if $k$ is even, then

$$\sum_{n \ge M} \frac{\sum_{j=0}^{m} (-1)^j \binom{2m+1}{j} f_{(2n+1)(2m+1-2j)} f_{k(2m+1-2j)}}
{\left(\ell_{2n+1}^2 - (x^2 + 4) f_k^2\right)^{2m+1}}
= \frac{1}{x^2 + 4} \sum_{r=1}^{k} \frac{1}{\ell_{2r-1}^{2m+1}}.$$

## Sources

- Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article linzhou02172024, Theorem 1.8.
