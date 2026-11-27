# Doob's $L^2$ maximal inequality for right-continuous martingales

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $M=(M_t)_{t\ge0}$ a real martingale with right-continuous paths. If $T\ge0$ and $\mathbb E M_T^2<\infty$, then

$$\mathbb E\Bigl[\sup_{0\le t\le T}M_t^2\Bigr]\le4\,\mathbb E\bigl[M_T^2\bigr].$$

## Proof depends on

- [Doob's L² maximal inequality, finite horizon](../doob-s-maximal-inequalities/doob-sq-maximal-ineq.md)

## Expansion

A proof page must apply the discrete-time inequality to the martingale sampled at the finite sets $D_n=\{kT2^{-n}:0\le k\le2^n\}$, which increase to a countable dense subset of $[0,T]$ containing $T$; identify $\sup_{t\le T}\lvert M_t\rvert$ with the supremum over $\bigcup_nD_n$ by right-continuity of the paths, which also makes the supremum measurable; and conclude by monotone convergence. It should note that square integrability of $M_t$ for $t\le T$ follows from that of $M_T$ by Jensen's inequality for conditional expectations.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Chapter 1, Section 3.
- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 3.
