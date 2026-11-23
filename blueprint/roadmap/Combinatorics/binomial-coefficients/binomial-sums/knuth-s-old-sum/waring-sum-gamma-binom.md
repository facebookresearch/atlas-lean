# Waring-type sum of generalized central binomial coefficients

Write
$\binom{a}{b} = \Gamma(a+1)/(\Gamma(b+1)\,\Gamma(a-b+1))$ for the generalized binomial
coefficient. For every integer $n \ge 1$ and every real number $v > -1$,

$$
\sum_{k=0}^{\lfloor n/2 \rfloor} (-1)^k \frac{n}{n-k} \binom{n-k}{k} 2^{-4k}
\binom{2k+v}{(2k+v)/2} =
\binom{2n+v}{(2n+v)/2} \binom{v}{v/2} \, 2^{1-2n} \binom{n+v}{v/2}^{-1}.
$$

The paper states this for every non-negative integer $n$, but at $n = 0$ the factor
$n/(n-k)$ is $0/0$, and the paper derives the identity from Waring's formula, which it
states for positive $n$ only.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 20.
