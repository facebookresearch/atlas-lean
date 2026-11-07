# Alternating reciprocal generalized-binomial sums from a polynomial identity

Write $\binom{u}{w} = \Gamma(u+1)/(\Gamma(w+1)\,\Gamma(u-w+1))$ for the generalized binomial
coefficient of complex numbers $u$ and $w$. Let $s, n, m, r$ be natural numbers, let
$f, g \colon \mathbb{N} \to \mathbb{C}$ and $p, q \colon \mathbb{N} \to \mathbb{N}$ satisfy

$$\sum_{k=s}^{n} f(k)\,(1+t)^{p(k)} = \sum_{k=m}^{r} g(k)\, t^{q(k)}
\quad \text{for all } t \in \mathbb{C},$$

and let $u, v$ be complex numbers with $\operatorname{Re} v > -1$,
$\operatorname{Re} u - p(j) > -1$ for $s \le j \le n$ and $\operatorname{Re} u - q(j) > -1$ for
$m \le j \le r$. Then

$$\sum_{k=s}^{n} (-1)^{p(k)} f(k) \binom{u+v}{u-p(k)}^{-1}
= \frac{u+v+1}{v+1} \sum_{k=m}^{r} (-1)^{q(k)} g(k) \binom{u-q(k)+v+1}{v+1}^{-1}.$$

This is the paper's equation (34) corrected. The paper prints the last binomial as
$\binom{u-q(k)+1}{v+1}$; that is false (for the identity $1 = 1$, that is $f = g = 1$ and
$p = q = 0$, at $u = v = 1$ the left side is $1/2$ and the printed right side $3/2$), and the
paper's own proof (integration against $(1-x)^v$ with the Beta integral) gives the reading
stated here, which agrees with the printed one at $v = 0$.

## Sources

- Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related Sums*, INTEGERS 26 (2026), Article A19, Theorem 9 (`integers-2026-A19-thm-9`).
