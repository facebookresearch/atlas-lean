# Extension of the stochastic integral against a continuous square-integrable martingale to $L^2(d\langle M\rangle\otimes d\mathbb P)$

Let $M$ be a continuous $(\mathcal F_t)$-martingale on $[0,T]$ with $\mathbb E M_T^2<\infty$, so $\mathbb E\langle M\rangle_T<\infty$. Let $H$ be an $(\mathcal F_t)$-progressive process with

$$\mathbb E\int_0^TH_s^2\,d\langle M\rangle_s<\infty .$$

Then $H$ is the limit in $L^2(d\langle M\rangle\otimes d\mathbb P)$ on $(0,T]\times\Omega$ of [elementary integrands](elementary-integrand.md) $H^{(n)}$. For any such sequence, the [elementary integrals](elementary-stochastic-integral-against-a-continu.md) $\int_0^\cdot H^{(n)}\,dM$ converge in $L^2(\mathbb P)$ uniformly on $[0,T]$, and the limit $\int_0^\cdot H\,dM$ does not depend on the sequence up to indistinguishability. It is a continuous square-integrable martingale on $[0,T]$, linear in $H$, with

$$\mathbb E\Bigl[\Bigl(\int_0^tH\,dM\Bigr)^2\Bigr]=\mathbb E\int_0^tH_s^2\,d\langle M\rangle_s,\qquad0\le t\le T .$$

## Depends on

- [Elementary stochastic integral against a continuous square-integrable martingale and its isometry](elementary-stochastic-integral-against-a-continu.md)
- [Elementary integrand](elementary-integrand.md)

## Expansion

A full proof page must establish:

- Density of elementary integrands among progressive processes in $L^2(d\langle M\rangle\otimes d\mathbb P)$ for continuous $\langle M\rangle$ (a time change by $\langle M\rangle$ reduces it to the case of Lebesgue measure).
- Doob's $L^2$ maximal inequality and the elementary isometry: the elementary integrals form a Cauchy sequence in $L^2(\mathbb P;C[0,T])$, and continuity, the martingale property, linearity and the isometry pass to the limit.
- For $M$ a Brownian motion, the construction agrees almost surely with the Brownian Itô integral built from [density of elementary integrands](is-ito-approximable-of-is-progressive.md) and the [elementary Itô integral](ito-integral.md).

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Sec. 3.2.
