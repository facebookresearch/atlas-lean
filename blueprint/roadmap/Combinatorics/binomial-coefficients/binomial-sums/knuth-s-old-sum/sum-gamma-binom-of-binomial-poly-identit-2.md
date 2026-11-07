# Central binomial sums from a polynomial identity: right exponents odd at even indices

Write $\binom{u}{w} = \Gamma(u+1)/(\Gamma(w+1)\Gamma(u-w+1))$ for the generalized binomial
coefficient of complex $u$, $w$. Let $s, n, m, r$ be natural numbers, let $f, g$ be
complex-valued functions and $p, q$ natural-number-valued functions on the natural numbers, and
suppose that for every complex $t$,

$$
\sum_{k=s}^{n} f(k) (1+t)^{p(k)} = \sum_{k=m}^{r} g(k) t^{q(k)}.
$$

Suppose also that $q(2j)$ is odd whenever $m \le 2j \le r$, and $q(2j+1)$ is even whenever
$m \le 2j+1 \le r$. Then for every complex $v$ with $\operatorname{Re} v > -1$,

$$
\sum_{k=s}^{n} \frac{f(k)}{2^{p(k)}} \binom{2p(k)+v}{(2p(k)+v)/2} \binom{p(k)+v}{v/2}^{-1}
= \sum_{k=\lfloor (m+2)/2 \rfloor}^{\lfloor (r+1)/2 \rfloor} \frac{g(2k-1)}{2^{q(2k-1)}}
\binom{q(2k-1)}{q(2k-1)/2} \binom{(q(2k-1)+v)/2}{v/2}^{-1}.
$$

This is equation (37) of the source.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 11, part 1 (`integers-2026-A19-thm-11`).
