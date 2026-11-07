# Central binomial transform of a polynomial identity with exponents $k$

Let
$s, n, m, r$ be natural numbers and $f, g : \mathbb{N} \to \mathbb{C}$ such that
$\sum_{k=s}^{n} f(k) (1+t)^{k} = \sum_{k=m}^{r} g(k) t^{k}$ for every complex $t$. Then for
every real $v > -1$,

$$
\sum_{k=s}^{n} \frac{f(k)}{2^{k}} \binom{2k+v}{(2k+v)/2} \binom{k+v}{v/2}^{-1}
= \sum_{k=\lfloor (m+1)/2 \rfloor}^{\lfloor r/2 \rfloor} \frac{g(2k)}{2^{2k}} \binom{2k}{k}
\binom{(2k+v)/2}{v/2}^{-1},
$$

where $\binom{2k}{k}$ is the central binomial coefficient and otherwise
$\binom{a}{b} = \Gamma(a+1)/(\Gamma(b+1)\Gamma(a-b+1))$ is the generalized binomial
coefficient of complex numbers $a, b$.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Corollary 3.
