# Lévy's characterization of multidimensional Brownian motion

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $M=(M^1,\ldots,M^d)$ an $\mathbb R^d$-valued process whose coordinates are continuous $(\mathcal F_t)$-local martingales with $M_0=0$. Suppose the quadratic covariations satisfy

$$\langle M^i,M^j\rangle_t=\delta_{ij}\,t\qquad(t\ge0,\ 1\le i,j\le d).$$

Then $M$ is a standard $d$-dimensional $(\mathcal F_t)$-[Brownian motion](multidimensional-brownian-motion.md): each coordinate is a real Brownian motion, the coordinates are independent, and for $0\le s\le t$ the increment $M_t-M_s$ is independent of $\mathcal F_s$ with law $\mathcal N(0,(t-s)I_d)$.

For $d=1$ and $M$ a true martingale with $M_t^2-t$ a martingale, this is [Lévy's characterisation of Brownian motion](../it-s-formula/is-brownian-real-of-martingale-sq-sub.md).

## Depends on

- [Multidimensional Brownian motion](multidimensional-brownian-motion.md)
- [Quadratic variation process $\langle M\rangle$ for continuous local martingales](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md)

## Proof depends on

- [Itô's formula for continuous semimartingales with bounded derivatives](../it-s-formula/ito-formula-for-continuous-semimartingales-bound.md)
- [Existence of Brownian motion](exists-is-brownian-real.md)
- [Lévy's continuity theorem](../../characteristic-functions/levy-continuity-theorem/levy-continuity-of-char-fun.md)

## Expansion

A full proof page must establish the following.

- For fixed $u\in\mathbb R^d$, apply [Itô's formula for continuous semimartingales](../it-s-formula/ito-formula-for-continuous-semimartingales-bound.md), in its complex-valued and multidimensional form, to $Z_t=\exp\bigl(i\langle u,M_t\rangle+\frac12|u|^2t\bigr)$: the finite-variation terms cancel because $\langle M^i,M^j\rangle_t=\delta_{ij}t$, so $Z$ is a continuous local martingale; it is bounded on bounded time intervals, hence a martingale.
- Hence $\mathbb E[\exp(i\langle u,M_t-M_s\rangle)\mid\mathcal F_s]=\exp(-\frac12|u|^2(t-s))$, which identifies the conditional law of the increment as $\mathcal N(0,(t-s)I_d)$ and gives independence of $\mathcal F_s$.
- Independent Gaussian increments and continuous paths make $M$ a standard Brownian motion, with independent coordinates because the covariance matrix is diagonal.
- The one-dimensional martingale case as a special case.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren der mathematischen Wissenschaften 293, Springer (1999), <https://link.springer.com/book/10.1007/978-3-662-06400-9>, Lévy's characterization (statement and proof).
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Section 3.3 (statement and proof).
