# Central binomial sums from a polynomial identity: left exponents even at even indices

Write $\binom{u}{w} = \Gamma(u+1)/(\Gamma(w+1)\Gamma(u-w+1))$ for the generalized binomial
coefficient of complex $u$, $w$. Let $s, n, m, r$ be natural numbers, let $f, g$ be
complex-valued functions and $p, q$ natural-number-valued functions on the natural numbers, and
suppose that for every complex $t$,

$$
\sum_{k=s}^{n} f(k) (1+t)^{p(k)} = \sum_{k=m}^{r} g(k) t^{q(k)}.
$$

Suppose also that $p(2j)$ is even whenever $s \le 2j \le n$, and $p(2j+1)$ is odd whenever
$s \le 2j+1 \le n$. Then for every complex $v$ with $\operatorname{Re} v > -1$,

$$
\sum_{k=m}^{r} \frac{(-1)^{q(k)} g(k)}{2^{q(k)}} \binom{2q(k)+v}{(2q(k)+v)/2}
\binom{q(k)+v}{v/2}^{-1}
= \sum_{k=\lfloor (s+1)/2 \rfloor}^{\lfloor n/2 \rfloor} \frac{(-1)^{p(2k)} f(2k)}{2^{p(2k)}}
\binom{p(2k)}{p(2k)/2} \binom{(p(2k)+v)/2}{v/2}^{-1}.
$$

This is equation (38) of the source.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 11, part 2 (`integers-2026-A19-thm-11`).
