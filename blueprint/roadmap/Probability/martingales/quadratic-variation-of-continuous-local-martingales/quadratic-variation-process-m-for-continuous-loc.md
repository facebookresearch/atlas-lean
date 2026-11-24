# Quadratic variation of continuous local martingales

Let $M$ be a [continuous local martingale](local-martingales-and-localization.md) with $M_0=0$ with respect to a filtration satisfying the usual conditions, and let $\tau_n=\inf\{t:|M_t|\ge n\}$. On $[0,\tau_n]$ the stopped martingale $M^{\tau_n}$ is bounded, and its [dyadic quadratic variation](dyadic-quadratic-variation-of-bounded-continuous.md) has a limit $\langle M^{\tau_n}\rangle$; these limits are consistent in $n$ and define a process $\langle M\rangle$ with the following properties:

1. $\langle M\rangle$ is continuous, nondecreasing and adapted, with $\langle M\rangle_0=0$;
2. $M^2-\langle M\rangle$ is a continuous local martingale;
3. $\langle M\rangle$ is unique up to indistinguishability among processes with properties 1 and 2;
4. if $M$ is bounded, or if $\mathbb E\sup_{t\le T}M_t^2<\infty$ for every $T$, then $M^2-\langle M\rangle$ is a martingale and $\mathbb E M_T^2=\mathbb E\langle M\rangle_T$.

For two continuous local martingales $M,N$ vanishing at $0$, polarization $\langle M,N\rangle=\frac14(\langle M+N\rangle-\langle M-N\rangle)$ gives the unique continuous adapted finite-variation process with $MN-\langle M,N\rangle$ a continuous local martingale.

## Depends on

- [Local martingales and localization](local-martingales-and-localization.md)
- [Dyadic quadratic variation of bounded continuous martingales](dyadic-quadratic-variation-of-bounded-continuous.md)

## Proof depends on

- [Itô processes and their quadratic variation](../../stochastic-calculus/it-s-formula/ito-processes-and-their-quadratic-variation.md)

## Expansion

A full proof shows consistency of the localized limits, uniqueness from the fact that a continuous local martingale of finite variation vanishing at $0$ is identically $0$ (shared with [Itô processes and their quadratic variation](../../stochastic-calculus/it-s-formula/ito-processes-and-their-quadratic-variation.md)), and item 4 by monotone and dominated convergence. It should check $\langle B\rangle_t=t$ for Brownian motion $B$, and the guard example $M_t=ZB_t$ with $Z$ independent of $B$, $\mathcal F_0$-measurable and $\mathbb EZ^2=\infty$: then $\langle M\rangle_t=Z^2t$ and $M_t^2-\langle M\rangle_t$ is not integrable, so only the local-martingale conclusion holds.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren 293, Springer, 1999, <https://link.springer.com/book/10.1007/978-3-662-06400-9>, bracket of continuous local martingales (topic).
