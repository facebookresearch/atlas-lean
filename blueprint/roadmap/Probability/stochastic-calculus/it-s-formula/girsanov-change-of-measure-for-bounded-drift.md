# Girsanov's theorem for bounded progressive drift

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $B$ a real $(\mathcal F_t)$-Brownian motion: adapted, with continuous paths, $B_0=0$, and each increment $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$ with law $\mathcal N(0,t-s)$. Let $\theta$ be progressively measurable with $|\theta_s|\le C$, fix $T>0$, let $Z$ be the [exponential martingale](exponential-martingale-for-bounded-integrands.md) $Z_t=\exp\bigl(\int_0^t\theta\,dB-\frac12\int_0^t\theta^2ds\bigr)$, and define the probability measure $\mathbb Q$ on $\mathcal F_T$ by $d\mathbb Q=Z_T\,d\mathbb P$. Then

$$W_t=B_t-\int_0^t\theta_s\,ds,\qquad0\le t\le T,$$

is an $(\mathcal F_t)$-Brownian motion on $[0,T]$ under $\mathbb Q$: for $0\le s\le t\le T$ and $u\in\mathbb R$,

$$\mathbb E_{\mathbb Q}\bigl[e^{iu(W_t-W_s)}\bigm|\mathcal F_s\bigr]=e^{-u^2(t-s)/2}\qquad\mathbb Q\text{-almost surely}.$$

For constant $\theta\equiv\mu$ this is [Girsanov's theorem for a constant drift](../has-law-sub-drift-with-density.md).

Application to Wright–Fisher diffusions. For genic selection without mutation, the drift $b(x)=\alpha x(1-x)$ and diffusion coefficient $\sigma(x)=\sqrt{x(1-x)}$ give $b/\sigma=\alpha\sqrt{x(1-x)}$, extended by $0$ at $x\in\{0,1\}$, which is bounded by $|\alpha|/2$; so $\theta_s=(b/\sigma)(X_s)$ satisfies the hypothesis along any $[0,1]$-valued path. With two-way mutation, the drift $\frac12\bigl(\vartheta_1(1-x)-\vartheta_2x\bigr)$ divided by $\sqrt{x(1-x)}$ is unbounded near $0$ when $\vartheta_1>0$ and near $1$ when $\vartheta_2>0$; there the bounded-drift hypothesis fails and a localization argument is required.

## Depends on

- [Exponential martingale for bounded integrands](exponential-martingale-for-bounded-integrands.md)

## Proof depends on

- [Itô's formula for Itô processes with locally integrable coefficients](ito-formula-for-ito-processes-time-dependent-loc.md)
- [Optional stopping theorem in continuous time](../../martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)

## Expansion

A full proof page must establish the following.

- $\mathbb Q$ is a probability measure because $\mathbb EZ_T=1$, and $\mathbb Q$-conditional expectations are given by the Bayes formula $\mathbb E_{\mathbb Q}[Y\mid\mathcal F_s]=\mathbb E[YZ_t\mid\mathcal F_s]/Z_s$ for $\mathcal F_t$-measurable bounded $Y$, using the martingale property of $Z$ and [optional stopping](../../martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md) in its conditional form.
- The characteristic-function identity: apply [Itô's formula for Itô processes](ito-formula-for-ito-processes-time-dependent-loc.md) to the product $Z_t\exp\bigl(iuW_t+\frac12u^2t\bigr)$ (real and imaginary parts); the drift terms cancel, so the product is a $\mathbb P$-martingale on $[0,T]$, bounded in $L^2$ by the bound on $\mathbb EZ_T^2$.
- Continuity of $W$ and the identity give independent Gaussian increments under $\mathbb Q$.
- The two Wright–Fisher computations.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren der mathematischen Wissenschaften 293, Springer (1999), <https://link.springer.com/book/10.1007/978-3-662-06400-9>, Girsanov's theorem (statement and proof).
