# Gronwall inequality in integral form

Let $a \in \mathbb{R}$, $K \ge 0$ and $T \in \mathbb{R}$, and let $u : \mathbb{R} \to \mathbb{R}$ be integrable on $[0, T]$ with $u(t) \ge 0$ for $t \in [0, T]$. If

$$u(t) \le a + K\int_0^t u(s)\,ds \qquad \text{for every } t \in [0, T],$$

then

$$u(t) \le a\,e^{Kt} \qquad \text{for every } t \in [0, T].$$

No continuity or boundedness of $u$ is assumed.

## Informally uses

- [Monotonicity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-mono.md)
- [Power series of the real exponential function](../../special-functions/elementary-transcendental-functions/real-exponential-power-series.md)

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, 1991, <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, the Gronwall lemma used for uniqueness of stochastic differential equations.
