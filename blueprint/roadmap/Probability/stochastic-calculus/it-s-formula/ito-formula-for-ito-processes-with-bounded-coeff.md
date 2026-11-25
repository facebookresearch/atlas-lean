# Itô's formula for Itô processes with bounded coefficients

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $B$ a real $(\mathcal F_t)$-Brownian motion: adapted, with continuous paths, $B_0=0$, and each increment $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$ with law $\mathcal N(0,t-s)$. Let

$$X_t=X_0+\int_0^tb_s\,ds+\int_0^t\sigma_s\,dB_s$$

be an [Itô process](ito-processes-and-their-quadratic-variation.md) with progressively measurable coefficients bounded by a constant, $|b_s|\le C$ and $|\sigma_s|\le C$, and an $\mathcal F_0$-measurable $X_0$. Let $f:[0,\infty)\times\mathbb R\to\mathbb R$ be $C^{1,2}$ with $f$, $\partial_tf$, $\partial_xf$ and $\partial_{xx}f$ bounded and continuous. Then for every $t\ge0$, almost surely,

$$f(t,X_t)=f(0,X_0)+\int_0^t\Bigl(\partial_tf(s,X_s)+b_s\,\partial_xf(s,X_s)+\frac12\sigma_s^2\,\partial_{xx}f(s,X_s)\Bigr)ds+\int_0^t\sigma_s\,\partial_xf(s,X_s)\,dB_s .$$

For $b=0$, $\sigma=1$ and $X_0=0$ this is [Itô's formula for $f(t,B_t)$](ito-formula-for-f-t-b-t-with-bounded-derivatives.md), and for time-independent $f$ the formula of [Itô's formula](ito-formula.md).

## Depends on

- [Itô processes and their quadratic variation](ito-processes-and-their-quadratic-variation.md)

## Proof depends on

- [Itô's formula for $f(t,B_t)$ with bounded derivatives](ito-formula-for-f-t-b-t-with-bounded-derivatives.md)

## Expansion

A full proof page must establish the following.

- Left-point approximation: telescope over partitions of $[0,t]$ and expand each increment to second order.
- The weighted quadratic-variation limit $\sum_kg(t_k)\bigl(\int_{t_k}^{t_{k+1}}\sigma\,dB\bigr)^2\to\int_0^tg(s)\sigma_s^2\,ds$ in probability for bounded continuous adapted $g$, using the Itô isometry and the bound $|\sigma|\le C$.
- Convergence of the first-order stochastic terms by the isometry, of the drift terms pathwise, and vanishing of the remainder by uniform continuity.
- Checks: the case $b=0$, $\sigma=1$; and for deterministic $\sigma$ with $b=0$, $X_0=0$, the formula applied to $x^2$ (after truncation) gives $\mathbb EX_t^2=\int_0^t\sigma_s^2\,ds$.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Itô's rule for continuous semimartingales (statement and proof).
