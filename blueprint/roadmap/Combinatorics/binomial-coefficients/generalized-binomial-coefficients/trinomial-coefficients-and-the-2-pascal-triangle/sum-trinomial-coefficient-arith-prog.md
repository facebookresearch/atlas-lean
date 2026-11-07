# Roots-of-unity filter for trinomial coefficients

Write $\binom{n}{k}_2$ for the trinomial
coefficient, the coefficient of $t^k$ in $(1 + t + t^2)^n$. Let $n$, $x$, $b$ be natural
numbers with $x < b$, let $z \ne 0$ be a complex number, and let $w = e^{2\pi i/b}$. Then

$$\sum_{k=0}^{\lfloor (2n - x)/b \rfloor} \binom{n}{x + bk}_2 z^{x + bk} =
\frac{z^n}{b} \sum_{j=1}^{b} w^{j(n - x)} \left(1 + z w^j + \frac{1}{z w^j}\right)^n,$$

where for $x > 2n$ the left side is $0$. The hypothesis $z \ne 0$ is implicit in the
paper's $(z w^j)^{-1}$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 9 (`jis-2025-25.3.5-thm-9`).
