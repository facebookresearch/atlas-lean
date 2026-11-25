# Shifted central binomial transform of a polynomial identity

Let $s, n, m, r$ be
natural numbers, $f, g : \mathbb{N} \to \mathbb{C}$ and $p, q : \mathbb{N} \to \mathbb{N}$
such that $\sum_{k=s}^{n} f(k) (1+t)^{p(k)} = \sum_{k=m}^{r} g(k) t^{q(k)}$ for every
complex $t$, and let $u, v$ be complex numbers with $\operatorname{Re} v > -1$,
$\operatorname{Re}(2(u-p(j))+v) > -1$ for $s \le j \le n$ and
$\operatorname{Re}(2(u-q(j))+v) > -1$ for $m \le j \le r$. Then

$$
\sum_{k=s}^{n} f(k)\, 2^{2p(k)} \binom{2(u-p(k))+v}{(2(u-p(k))+v)/2}
\binom{u-p(k)+v}{v/2}^{-1}
= \binom{v}{v/2}^{-1} \sum_{k=m}^{r} g(k) \binom{2(u-q(k))+v}{(2(u-q(k))+v)/2}
\binom{2q(k)+v}{(2q(k)+v)/2} \binom{u+v}{(2q(k)+v)/2}^{-1},
$$

where $\binom{a}{b} = \Gamma(a+1)/(\Gamma(b+1)\Gamma(a-b+1))$ is the generalized binomial
coefficient of complex numbers $a, b$.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 8.
