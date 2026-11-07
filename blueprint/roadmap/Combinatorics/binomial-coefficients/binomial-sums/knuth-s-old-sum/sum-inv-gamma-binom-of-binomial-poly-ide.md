# Reciprocal binomial transform of a polynomial identity

Let $s, n, m, r$ be natural
numbers, $f, g : \mathbb{N} \to \mathbb{C}$ and $p, q : \mathbb{N} \to \mathbb{N}$ such that
$\sum_{k=s}^{n} f(k) (1+t)^{p(k)} = \sum_{k=m}^{r} g(k) t^{q(k)}$ for every complex $t$. Then
for all complex numbers $u, v$ with $\operatorname{Re} u > -1$ and $\operatorname{Re} v > -1$,

$$
\sum_{k=s}^{n} f(k) \binom{p(k)+u+v+1}{u+1}^{-1}
= \frac{u+1}{v+1} \sum_{k=m}^{r} (-1)^{q(k)} g(k) \binom{q(k)+u+v+1}{v+1}^{-1},
$$

where $\binom{a}{b} = \Gamma(a+1)/(\Gamma(b+1)\Gamma(a-b+1))$ is the generalized binomial
coefficient of complex numbers $a, b$.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 7 (`integers-2026-A19-thm-7`).
