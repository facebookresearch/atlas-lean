# Even-power sums with even-index Lucas polynomial denominators

Let $f_n$ and $\ell_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, \ell\}$, evaluated at a real number
$x > 0$, and let $k$ and $m$ be positive integers. Put $L = (k + 1)/2$ and $s_r = 2r - 1$ if $k$
is odd, and $L = k/2 + 1$ and $s_r = 2r$ if $k$ is even. Then

$$\sum_{n \ge L} \frac{\sum_{j=0}^{m-1} \binom{2m}{j} (-1)^{kj} f_{2k(m-j)} f_{4n(m-j)}}
{\left(\ell_{2n}^2 + (-1)^k (x^2 + 4) f_k^2\right)^{2m}}
= \frac{1}{x^2 + 4} \sum_{r=1}^{k} \frac{1}{\ell_{s_r}^{2m}}.$$

## Sources

- Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article linzhou02172024, Theorem 1.2 (`fq-2024-linzhou02172024-thm-1.2`).
