# Recovering even coefficients from the 2-Pascal transform

Write $[t^m]F$ for the
coefficient of $t^m$ in a power series $F$. Let $S$, $Q$, $R$ be power series over $\mathbb{Q}$
with $S^2 = 4 - 3t^2$, $S(0) = 2$, $2Q^2 = 2 - t^2 - tS$, $Q(0) = 1$, $R^2 = 1 - t + t^2$ and
$R(0) = 1$, and put

$$\alpha = \frac{-2(2Q + t^2 S - t)}{Q(3t^4 + 2tS - t^2 - 4)}, \qquad
\beta = \frac{t(t + S)}{2(1 - t^2)}.$$

For a power series $f$ over $\mathbb{Q}$ let $g(t) = \alpha(t)\,f(\beta(t))$. Then for every
$n \in \mathbb{N}$,

$$[t^{2n}]\,f = [t^{2n}]\,\frac{(2 - t)(1 - t)^{2n}}{2(1 - t + t^2)}\,g\!\left(\frac{t}{R}\right).$$

Here $S$, $Q$, $R$ are the square roots $\sqrt{4 - 3t^2}$, $\sqrt{(2 - t^2 - tS)/2}$ and
$\sqrt{1 - t + t^2}$, and $\alpha$, $\beta$ are the series of the paper's Theorem 6.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Corollary 49 (`jis-2025-25.3.5-cor-49`).
