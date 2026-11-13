# Alternating trinomial sums over residue classes modulo 3 and 5

Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$, and
$L_m$ for the Lucas numbers ($L_0 = 2$, $L_1 = 1$, $L_{m+2} = L_{m+1} + L_m$). Let $n$ and $x$ be
natural numbers.

If $x < 3$, then $3 \sum_{k=0}^{2n} (-1)^{k+x} \binom{n}{3k+x}_2$ equals $(-1)^n 2^{n+1} + 1$
when $n \equiv x \pmod 3$, and $(-1)^{n+1} 2^n + 1$ otherwise.

If $x < 5$, let $S = 5 \sum_{k=0}^{2n} (-1)^{k+x} \binom{n}{5k+x}_2$. Then
$S = 2 (-1)^n L_{2n} + 1$ when $n \equiv x \pmod 5$, $S = (-1)^{n+1} L_{2n+1} + 1$ when
$n \equiv x \pm 1 \pmod 5$, and $S = (-1)^n L_{2n-1} + 1$ when $n \ge 1$ and
$n \equiv x \pm 2 \pmod 5$.

The paper does not bound $x$; the last case excludes $n = 0$, where it would need $L_{-1}$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 10 (`jis-2025-25.3.5-cor-10`).
