# Most units give a factor in Shor's reduction

Let $n$ be an odd positive integer with $k$ distinct prime factors. Among the units $x$ modulo
$n$, those whose multiplicative order $r$ is even and satisfies $x^{r/2} \not\equiv -1 \pmod n$
form a fraction at least $1 - 1/2^{k-1}$ of all units, where $k - 1$ is read as $0$ when $k = 0$ (that is, $n = 1$):

$$\#\{x \in (\mathbb{Z}/n\mathbb{Z})^{\times} : r \text{ even},\ x^{r/2} \ne -1\} \ \ge\ \Big(1 - \frac{1}{2^{k-1}}\Big)\, \varphi(n).$$

For each such $x$, [Shor's order-to-factor reduction](gcd-factor-of-order.md) makes
$\gcd(x^{r/2} - 1, n)$ a nontrivial factor of $n$. So a random unit yields a factor with
probability at least $1 - 1/2^{k-1}$, which is at least $1/2$ when $n$ is not a prime power
(for prime powers, $k = 1$, the bound is empty, and Shor factors them classically).

Shor's proof sketch: write $n = \prod_i p_i^{a_i}$ and let $r_i$ be the order of $x$ modulo
$p_i^{a_i}$, so that $r = \operatorname{lcm}(r_i)$. The procedure fails only if the largest
powers of $2$ dividing the $r_i$ all agree. By the Chinese remainder theorem a random $x$ is a
tuple of independent random $x_i$, and since each $(\mathbb{Z}/p_i^{a_i}\mathbb{Z})^{\times}$ is
cyclic, each power of $2$ agrees with the previous ones with probability at most $1/2$.

For example, for $n = 15$ ($k = 2$) six of the eight units ($2, 4, 7, 8, 11, 13$) are good,
against the bound $4$.

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509, arXiv:quant-ph/9508027, Section 5, second and third paragraphs (Shor attributes the reduction to G. L. Miller, 1976).
