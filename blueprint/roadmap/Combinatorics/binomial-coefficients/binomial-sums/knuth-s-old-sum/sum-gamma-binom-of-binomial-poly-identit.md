# Central binomial transform of a polynomial identity, even exponents at even indices

Let $s, n, m, r$ be natural numbers, $f, g : \mathbb{N} \to \mathbb{C}$ and
$p, q : \mathbb{N} \to \mathbb{N}$ such that
$\sum_{k=s}^{n} f(k) (1+t)^{p(k)} = \sum_{k=m}^{r} g(k) t^{q(k)}$ for every complex $t$.
Suppose that $q(2j)$ is even whenever $m \le 2j \le r$ and $q(2j+1)$ is odd whenever
$m \le 2j+1 \le r$. Then for every complex $v$ with $\operatorname{Re} v > -1$,

$$
\sum_{k=s}^{n} \frac{f(k)}{2^{p(k)}} \binom{2p(k)+v}{(2p(k)+v)/2} \binom{p(k)+v}{v/2}^{-1}
= \sum_{k=\lfloor (m+1)/2 \rfloor}^{\lfloor r/2 \rfloor} \frac{g(2k)}{2^{q(2k)}}
\binom{q(2k)}{q(2k)/2} \binom{(q(2k)+v)/2}{v/2}^{-1},
$$

where $\binom{a}{b} = \Gamma(a+1)/(\Gamma(b+1)\Gamma(a-b+1))$ is the generalized binomial
coefficient of complex numbers $a, b$.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 11, part 1.
