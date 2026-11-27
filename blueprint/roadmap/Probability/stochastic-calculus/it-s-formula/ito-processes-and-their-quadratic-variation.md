# Itô processes and their quadratic variation

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $B$ a real $(\mathcal F_t)$-Brownian motion: adapted, with continuous paths, $B_0=0$, and each increment $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$ with law $\mathcal N(0,t-s)$. An Itô process is a real process of the form

$$X_t=X_0+\int_0^tb_s\,ds+\int_0^t\sigma_s\,dB_s,\qquad t\ge0,$$

where $X_0$ is $\mathcal F_0$-measurable, and $b$ and $\sigma$ are progressively measurable processes with $\int_0^t|b_s|\,ds<\infty$ and $\int_0^t\sigma_s^2\,ds<\infty$ almost surely for every $t$; the first integral is a pathwise Lebesgue integral and the second is the [localized Itô integral](../it-integral/localized-ito-integral-and-integrals-up-to-stopp.md). $X$ has continuous paths and is adapted.

1. **Quadratic variation.** For every $t$ and every sequence of partitions $0=t_0<\cdots<t_m=t$ of $[0,t]$ with mesh tending to $0$,

    $$\sum_{k}\bigl(X_{t_{k+1}}-X_{t_k}\bigr)^2\longrightarrow[X]_t=\int_0^t\sigma_s^2\,ds\qquad\text{in probability}.$$

2. **Uniqueness of the decomposition.** If $X_0+\int_0^tb_s\,ds+\int_0^t\sigma_s\,dB_s=X'_0+\int_0^tb'_s\,ds+\int_0^t\sigma'_s\,dB_s$ for all $t$ almost surely, with $(b',\sigma')$ satisfying the same hypotheses, then $X_0=X'_0$ almost surely, $b=b'$ and $\sigma=\sigma'$ $\,ds\otimes d\mathbb P$-almost everywhere.

## Depends on

- [Localized Ito integral and integrals up to stopping times](../it-integral/localized-ito-integral-and-integrals-up-to-stopp.md)

## Proof depends on

- [Local martingales and localization](../../martingales/quadratic-variation-of-continuous-local-martingales/local-martingales-and-localization.md)

## Expansion

A full proof page must establish the following.

- Continuity and adaptedness of $X$.
- Item 1: the finite-variation part contributes nothing to the limit; for the stochastic integral, localize to stopping times at which $\int_0^\cdot\sigma^2ds$ is bounded, prove the $L^2$ statement there, and remove the localization.
- Item 2: the difference $\int_0^\cdot(\sigma_s-\sigma'_s)\,dB_s=\int_0^\cdot(b'_s-b_s)\,ds$ is a continuous local martingale of finite variation started at $0$, hence identically zero; its quadratic variation $\int_0^t(\sigma-\sigma')^2ds$ then vanishes, and the drifts agree as derivatives of equal absolutely continuous functions. This uses that a continuous local martingale of finite variation is constant.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Chapter 3, continuous semimartingales (definition and statement).
