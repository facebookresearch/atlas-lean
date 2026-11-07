# Double-factorial sums as derivatives of arcsine quotients

Let $n$ be a natural number.
If $n$ is odd, the $n$th derivative at $0$ of $x \mapsto \arcsin x / (1 - x)$ is

$$n! \sum_{j=0}^{(n-1)/2} \frac{(2j-1)!!}{(2j)!!\,(2j+1)},$$

and if $n \ge 2$ is even, the $n$th derivative at $0$ of $x \mapsto (\arcsin x)^2 / (2(1 - x))$ is

$$n! \sum_{j=0}^{(n-2)/2} \frac{(2j)!!}{(2j+1)!!\,(2j+2)},$$

where $(-1)!! = 1$ and $0!! = 1$.

These are the $n$th terms of the exponential generating functions of $\arcsin x / (1 - x)$
(OEIS A296726) and of $(\arcsin x)^2 / (2(1 - x))$ (OEIS A372324).

## Sources

- Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*, Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4 (`jis-2025-25.2.3-thm-4`).
