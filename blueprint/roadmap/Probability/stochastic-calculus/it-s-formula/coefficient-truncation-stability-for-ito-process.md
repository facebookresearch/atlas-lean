# Coefficient truncation stability for Itô processes

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $B$ a real $(\mathcal F_t)$-Brownian motion: adapted, with continuous paths, $B_0=0$, and each increment $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$ with law $\mathcal N(0,t-s)$. Let $X_t=X_0+\int_0^tb_s\,ds+\int_0^t\sigma_s\,dB_s$ be an [Itô process](ito-processes-and-their-quadratic-variation.md): $b,\sigma$ progressively measurable with $\int_0^t|b_s|\,ds<\infty$ and $\int_0^t\sigma_s^2\,ds<\infty$ almost surely for every $t$. For $n\ge1$ let

$$\tau_n=\inf\Bigl\{t\ge0:\ \int_0^t|b_s|\,ds+\int_0^t\sigma_s^2\,ds+|X_t|\ge n\Bigr\},$$

and for $K>0$ let $b^K=b\,\mathbf 1_{\{|b|\le K\}}$, $\sigma^K=\sigma\,\mathbf 1_{\{|\sigma|\le K\}}$ and $X^K_t=X_0+\int_0^tb^K_s\,ds+\int_0^t\sigma^K_s\,dB_s$. Then for every $n$ and $T>0$, as $K\to\infty$,

$$\sup_{t\le T}\Bigl|\int_0^{t\wedge\tau_n}b^K_s\,ds-\int_0^{t\wedge\tau_n}b_s\,ds\Bigr|\to0\ \text{almost surely},\qquad \sup_{t\le T}\Bigl|\int_0^{t\wedge\tau_n}\sigma^K_s\,dB_s-\int_0^{t\wedge\tau_n}\sigma_s\,dB_s\Bigr|\to0\ \text{in probability},$$

and for every $f\in C^{1,2}([0,\infty)\times\mathbb R)$ Itô's formula for $f(t\wedge\tau_n,X^K_{t\wedge\tau_n})$, with coefficients $(b^K,\sigma^K)$, converges term by term in probability, uniformly on $[0,T]$, to the corresponding expression for $f(t\wedge\tau_n,X_{t\wedge\tau_n})$ with coefficients $(b,\sigma)$.

The stopping at $\tau_n$ controls the integrals of the coefficients but not the coefficients themselves. For the deterministic $\sigma_s=s^{-1/4}$ and $b=0$, $\sigma$ is unbounded near $0$ but $\int_0^t\sigma_s^2\,ds=2\sqrt t$; no stopping time that is positive with positive probability bounds $\sigma$ on $[0,\tau]$, and the truncations satisfy $\mathbb E\bigl(\int_0^t\sigma^K\,dB-\int_0^t\sigma\,dB\bigr)^2=2K^{-2}\to0$ for $t\ge K^{-4}$, recovering the Wiener integral $\int_0^t s^{-1/4}dB_s\sim\mathcal N(0,2\sqrt t)$.

## Depends on

- [Itô processes and their quadratic variation](ito-processes-and-their-quadratic-variation.md)
- [Localized Ito integral and integrals up to stopping times](../it-integral/localized-ito-integral-and-integrals-up-to-stopp.md)

## Proof depends on

- [Itô's formula for Itô processes with bounded coefficients](ito-formula-for-ito-processes-with-bounded-coeff.md)

## Expansion

A full proof page must establish the following.

- The drift term by dominated convergence on $[0,\tau_n]$, where $\int_0^{\tau_n}|b|\,ds\le n$.
- The martingale term by Doob's $L^2$ maximal inequality and the isometry: $\mathbb E\sup_{t\le T}|\int_0^{t\wedge\tau_n}(\sigma^K-\sigma)dB|^2\le4\,\mathbb E\int_0^{T\wedge\tau_n}\sigma^2\mathbf 1_{\{|\sigma|>K\}}ds\to0$ by dominated convergence with bound $n$.
- Uniform convergence of $X^K$ to $X$ on $[0,T\wedge\tau_n]$ along a subsequence almost surely; hence $X^K$ eventually stays in $[-n-1,n+1]$ there, where $f$ and its derivatives are bounded and uniformly continuous; convergence of each term of Itô's formula, applying the [bounded-coefficient formula](ito-formula-for-ito-processes-with-bounded-coeff.md) to a $C^{1,2}_b$ modification of $f$ that agrees with $f$ on $[0,T]\times[-n-1,n+1]$.
- The deterministic example and its variance computation.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, localization of stochastic integrals (statement and proof).
