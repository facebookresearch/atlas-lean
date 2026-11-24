# Exponential martingale for bounded integrands

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $B$ a real $(\mathcal F_t)$-Brownian motion: adapted, with continuous paths, $B_0=0$, and each increment $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$ with law $\mathcal N(0,t-s)$. Let $\theta$ be a progressively measurable process with $|\theta_s|\le C$ for all $s$ and $\omega$, and fix a horizon $T>0$. Put

$$Z_t=\exp\Bigl(\int_0^t\theta_s\,dB_s-\frac12\int_0^t\theta_s^2\,ds\Bigr),\qquad 0\le t\le T .$$

Then:

1. $Z_t=1+\int_0^tZ_s\theta_s\,dB_s$ for all $t\le T$, almost surely;
2. $Z$ is a true martingale on $[0,T]$, and $\mathbb EZ_T=1$;
3. $\mathbb EZ_T^2\le e^{C^2T}$.

If $\theta$ is deterministic, $\int_0^T\theta\,dB\sim\mathcal N(0,v)$ with $v=\int_0^T\theta_s^2\,ds$, so $Z_T$ is lognormal with mean $1$.

## Proof depends on

- [Itô's formula for Itô processes with locally integrable coefficients](ito-formula-for-ito-processes-time-dependent-loc.md)
- [Localized Ito integral and integrals up to stopping times](../it-integral/localized-ito-integral-and-integrals-up-to-stopp.md)

## Expansion

A full proof page must establish the following.

- Item 1 from [Itô's formula for Itô processes](ito-formula-for-ito-processes-time-dependent-loc.md) applied to $e^x$ and the Itô process $Y_t=\int_0^t\theta\,dB-\frac12\int_0^t\theta^2ds$.
- Item 2: $Z$ is a nonnegative local martingale, hence a supermartingale; a uniform bound on $\mathbb EZ_t^2$ (item 3 for every $t$) gives $\mathbb E\int_0^TZ_s^2\theta_s^2\,ds<\infty$, so the stochastic integral is a square-integrable martingale. Alternatively Novikov's criterion holds trivially since $\int_0^T\theta^2\le C^2T$.
- Item 3: $Z_T^2=\exp\bigl(\int_0^T\theta^2ds\bigr)\,Z^{(2\theta)}_T\le e^{C^2T}Z^{(2\theta)}_T$, where $Z^{(2\theta)}$ is the exponential of $2\theta$, which has expectation at most $1$ as a nonnegative supermartingale.
- The deterministic case.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren der mathematischen Wissenschaften 293, Springer (1999), <https://link.springer.com/book/10.1007/978-3-662-06400-9>, exponential martingales (statement and proof).
