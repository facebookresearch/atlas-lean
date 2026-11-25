# Localized Itô integral and integrals up to stopping times

Let $B$ be a Brownian motion with respect to $(\mathcal F_t)$ and $H$ an $(\mathcal F_t)$-progressive process with

$$\int_0^tH_u^2\,du<\infty\quad\text{almost surely, for every }t\ge0 .$$

Put $\tau_n=\inf\{t\ge0:\int_0^tH_u^2\,du\ge n\}$, a sequence of stopping times increasing to $+\infty$ almost surely. The processes $H\mathbf 1_{[0,\tau_n]}$ satisfy $\mathbb E\int_0^\infty H_u^2\mathbf 1_{[0,\tau_n]}(u)\,du\le n$, so their Itô integrals are defined and have [continuous versions](ito-integral-continuous-modification.md) $I^{(n)}$; these are consistent, $I^{(n)}_t=I^{(m)}_t$ for $t\le\tau_n$ and $n\le m$, almost surely. The localized Itô integral

$$\int_0^tH\,dB=I^{(n)}_t\qquad\text{on }\{t\le\tau_n\}$$

is a well-defined continuous local martingale, localized by $(\tau_n)$. For every stopping time $\tau$,

$$\int_0^{t\wedge\tau}H\,dB=\int_0^tH\mathbf 1_{[0,\tau]}\,dB\qquad\text{for all }t,\ \text{almost surely}.$$

If $\mathbb E\int_0^tH_u^2\,du<\infty$ for every $t$, the localized integral agrees almost surely with the square-integrable [Itô integral](ito-integral-2.md).

## Depends on

- [Continuous modification of the Itô integral](ito-integral-continuous-modification.md)
- [Local martingales and localization](../../martingales/quadratic-variation-of-continuous-local-martingales/local-martingales-and-localization.md)

## Expansion

A full proof page must establish:

- $\tau_n$ are stopping times increasing to $+\infty$, from continuity and adaptedness of $t\mapsto\int_0^tH_u^2\,du$.
- The stopping identity for square-integrable integrands, $\int_0^{t\wedge\sigma}K\,dB=\int_0^tK\mathbf 1_{[0,\sigma]}\,dB$, first for elementary integrands and stopping times with finitely many values, then by approximation; consistency of the $I^{(n)}$ follows.
- The local-martingale property and the stopping identity for the localized integral.
- Agreement with the square-integrable integral under the integrability hypothesis.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Sec. 3.2.D (localization).
