# Trinomial coefficients from an algebraic Riordan array

Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$, and $[t^m]\,F$ for the
coefficient of $t^m$ in a formal power series $F$ over $\mathbb{Q}$. Let $S$ and $Q$ be power
series over $\mathbb{Q}$ with $S^2 = 4 - 3t^2$, $S(0) = 2$, $2Q^2 = 2 - t^2 - tS$ and $Q(0) = 1$,
and put

$$\alpha = \frac{-2\,(2Q + t^2 S - t)}{Q\,(3t^4 + 2tS - t^2 - 4)}, \qquad
\beta = \frac{t\,(t + S)}{2\,(1 - t^2)}.$$

Then $\binom{n}{k}_2 = [t^{2n}]\,\alpha\,\beta^k$ for all natural numbers $n$ and $k$.

In the paper $S = \sqrt{4 - 3t^2}$ and $\sqrt{2}\,Q = \sqrt{2 - t^2 - t\sqrt{4 - 3t^2}}$; since
$\sqrt{8 - 6t^2} = \sqrt{2}\,S$, the factors $\sqrt{2}$ in its formula for $\alpha$ cancel.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 6 (`jis-2025-25.3.5-thm-6`).
