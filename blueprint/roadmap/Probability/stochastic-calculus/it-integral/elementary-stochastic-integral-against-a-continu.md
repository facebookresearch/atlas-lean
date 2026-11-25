# Elementary stochastic integral against a continuous square-integrable martingale and its isometry

Let $M$ be a continuous $(\mathcal F_t)$-martingale with $\mathbb E M_t^2<\infty$ for every $t$, and let $\langle M\rangle$ be its [quadratic variation process](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md), so that $\mathbb E\langle M\rangle_t<\infty$. Let $H=\sum_{i=0}^{n-1}\xi_i\mathbf 1_{(t_i,t_{i+1}]}$ be an [elementary integrand](elementary-integrand.md): $0\le t_0\le\cdots\le t_n$ and each $\xi_i$ bounded and $\mathcal F_{t_i}$-measurable. Define

$$\int_0^tH\,dM=\sum_{i=0}^{n-1}\xi_i\bigl(M_{t_{i+1}\wedge t}-M_{t_i\wedge t}\bigr),\qquad t\ge0 .$$

Then $t\mapsto\int_0^tH\,dM$ is a continuous square-integrable $(\mathcal F_t)$-martingale, linear in $H$, and

$$\mathbb E\Bigl[\Bigl(\int_0^tH\,dM\Bigr)^2\Bigr]=\mathbb E\int_0^tH_s^2\,d\langle M\rangle_s=\mathbb E\sum_{i=0}^{n-1}\xi_i^2\bigl(\langle M\rangle_{t_{i+1}\wedge t}-\langle M\rangle_{t_i\wedge t}\bigr).$$

For $M$ a Brownian motion, $\langle M\rangle_t=t$ and this is the [Itô integral of an elementary integrand](ito-integral.md) with its isometry.

## Depends on

- [Quadratic variation process $\langle M\rangle$ for continuous local martingales](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md)
- [Elementary integrand](elementary-integrand.md)

## Proof depends on

- [Filtrations and stopping times](../../martingales/stopping-times-and-martingale-problems/filtrations-and-stopping-times.md)

## Expansion

A full proof page must establish:

- Continuity and square integrability, and the martingale property of each summand $\xi_i(M_{t_{i+1}\wedge t}-M_{t_i\wedge t})$, from boundedness and $\mathcal F_{t_i}$-measurability of $\xi_i$.
- Orthogonality of the summands, and $\mathbb E\bigl[\xi_i^2(M_b-M_a)^2\bigr]=\mathbb E\bigl[\xi_i^2(\langle M\rangle_b-\langle M\rangle_a)\bigr]$ for $t_i\le a\le b$, since $M^2-\langle M\rangle$ is a martingale.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Sec. 3.2 (integration with respect to continuous square-integrable martingales).
