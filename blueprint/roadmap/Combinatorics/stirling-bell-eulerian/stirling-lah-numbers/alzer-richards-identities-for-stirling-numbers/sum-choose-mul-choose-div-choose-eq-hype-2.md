# A binomial sum as a terminating ${}_2F_1$ series

Write
$x^{\overline{n}} = x(x+1)\cdots(x+n-1)$ for the rising factorial of a complex number $x$, and
$\binom{w}{k} = w(w-1)\cdots(w-k+1)/k!$ for a complex number $w$ and a natural number $k$. Let
$m$ and $\nu$ be natural numbers with $1 \le \nu \le \lfloor m/2 \rfloor$, and let $p$ be a
complex number with $p \ne -j$ for every natural number $j$ with $1 \le j \le \lfloor m/2 \rfloor$.
Then

$$
\sum_{k=0}^{\lfloor m/2 \rfloor} \frac{\binom{m-k}{k} \binom{m-\nu}{m-k}}{2^{2k} \binom{k+p}{k}} =
\frac{(m-\nu)!}{2^{2\nu} \, m!} \cdot \frac{(-m)^{\overline{2\nu}}}{(p+1)^{\overline{\nu}}}
\sum_{n=0}^{\lfloor m/2 \rfloor - \nu}
\frac{(\nu - m/2)^{\overline{n}} \, (\nu - (m-1)/2)^{\overline{n}}}
{(\nu + p + 1)^{\overline{n}} \, n!}.
$$

The last sum is the terminating hypergeometric series
${}_2F_1(\nu - m/2, \nu - (m-1)/2; \nu + p + 1; 1)$, whose terms vanish beyond
$n = \lfloor m/2 \rfloor - \nu$.

## Sources

- Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 9 (ii), Equation (16).
