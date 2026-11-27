# Itô's formula for Itô processes with locally integrable coefficients

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $B$ a real $(\mathcal F_t)$-Brownian motion: adapted, with continuous paths, $B_0=0$, and each increment $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$ with law $\mathcal N(0,t-s)$. Let $X_t=X_0+\int_0^tb_s\,ds+\int_0^t\sigma_s\,dB_s$ be an [Itô process](ito-processes-and-their-quadratic-variation.md) with progressively measurable $b$ and $\sigma$ such that $\int_0^t|b_s|\,ds<\infty$ and $\int_0^t\sigma_s^2\,ds<\infty$ almost surely for every $t$, and let $f\in C^{1,2}([0,\infty)\times\mathbb R)$, with no boundedness assumption. Then, almost surely, for all $t\ge0$,

$$f(t,X_t)=f(0,X_0)+\int_0^t\Bigl(\partial_tf(s,X_s)+b_s\,\partial_xf(s,X_s)+\frac12\sigma_s^2\,\partial_{xx}f(s,X_s)\Bigr)ds+\int_0^t\sigma_s\,\partial_xf(s,X_s)\,dB_s,$$

with the localized Itô integral. When $X=B$ and $f$ does not depend on $t$ and has bounded first and second derivatives, this is [Itô's formula](ito-formula.md).

Examples: for $f(x)=x^2$ and $X=B$, $B_t^2=2\int_0^tB_s\,dB_s+t$. If $X$ is a $[0,1]$-valued solution of $dX_t=\sqrt{X_t(1-X_t)}\,dB_t$ (the neutral Wright–Fisher diffusion), then $f(x)=x(1-x)$ gives

$$X_t(1-X_t)=X_0(1-X_0)+\int_0^t(1-2X_s)\sqrt{X_s(1-X_s)}\,dB_s-\int_0^tX_s(1-X_s)\,ds,$$

so the heterozygosity has drift $-X(1-X)$.

## Depends on

- [Itô processes and their quadratic variation](ito-processes-and-their-quadratic-variation.md)

## Proof depends on

- [Itô's formula for $f(t,B_t)$ with bounded derivatives](ito-formula-for-f-t-b-t-with-bounded-derivatives.md)
- [Itô's formula for Itô processes with bounded coefficients](ito-formula-for-ito-processes-with-bounded-coeff.md)
- [Usual conditions and continuous-time hitting times](../../markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/usual-conditions-and-continuous-time-hitting-tim.md)
- [Coefficient truncation stability for Itô processes](coefficient-truncation-stability-for-ito-process.md)

## Expansion

A full proof page must establish the following, in this order.

1. Energy localization: stop at the times $\tau_n$ of [coefficient truncation stability](coefficient-truncation-stability-for-ito-process.md), which bound $\int|b|$, $\int\sigma^2$ and $|X|$ but not $b$ or $\sigma$ themselves; compact-exit stopping on $|X|$ alone does not bound the coefficients.
2. Coefficient truncation to bounded $(b^K,\sigma^K)$ and the [bounded-coefficient formula](ito-formula-for-ito-processes-with-bounded-coeff.md).
3. The truncation limit $K\to\infty$ of coefficient truncation stability.
4. Compact modification of $f$: replace $f$ by a $C^{1,2}_b$ function equal to $f$ on $[0,T]\times[-n-1,n+1]$, and let $n\to\infty$ using $\tau_n\to\infty$.
5. Indistinguishability: both sides are continuous in $t$, so the identity holds for all $t$ simultaneously.
6. The two examples.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Itô's rule (statement and proof).
