# Stochastic integral against a continuous local martingale

Let $M$ be a continuous $(\mathcal F_t)$-local martingale with $M_0=0$ (for general $M_0$ apply the statement to $M-M_0$) and quadratic variation $\langle M\rangle$, and let $H$ be an $(\mathcal F_t)$-progressive process with

$$\int_0^tH_s^2\,d\langle M\rangle_s<\infty\quad\text{almost surely, for every }t\ge0 .$$

Then there is a continuous local martingale $\int_0^\cdot H\,dM$, null at $0$ and unique up to indistinguishability, such that for every localizing sequence of stopping times $\sigma_n\uparrow\infty$ with $M^{\sigma_n}$ a square-integrable martingale and $\mathbb E\int_0^{\sigma_n}H_s^2\,d\langle M\rangle_s<\infty$, the stopped process $\bigl(\int_0^\cdot H\,dM\bigr)^{\sigma_n}$ is the [$L^2$ stochastic integral](l2-d-m-x-dp-extension-of-the-stochastic-integral.md) of $H\mathbf 1_{[0,\sigma_n]}$ against $M^{\sigma_n}$. It satisfies

$$\Bigl\langle\int_0^\cdot H\,dM\Bigr\rangle_t=\int_0^tH_s^2\,d\langle M\rangle_s,\qquad \int_0^{t\wedge\tau}H\,dM=\int_0^tH\mathbf 1_{[0,\tau]}\,dM$$

for every stopping time $\tau$ and all $t$, almost surely. For $M=B$ a Brownian motion it agrees with the [localized Itô integral](localized-ito-integral-and-integrals-up-to-stopp.md).

## Depends on

- [Extension of the stochastic integral against a continuous square-integrable martingale to $L^2(d\langle M\rangle\otimes d\mathbb P)$](l2-d-m-x-dp-extension-of-the-stochastic-integral.md)
- [Local martingales and localization](../../martingales/quadratic-variation-of-continuous-local-martingales/local-martingales-and-localization.md)
- [Quadratic variation process $\langle M\rangle$ for continuous local martingales](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md)

## Expansion

A full proof page must establish:

- Existence of a localizing sequence, for example $\sigma_n=\inf\{t:|M_t|\ge n\text{ or }\int_0^tH_s^2\,d\langle M\rangle_s\ge n\}$.
- Consistency of the $L^2$ integrals along the localizing sequence (the stopping identity for $L^2$ integrands), giving a well-defined continuous local martingale independent of the localizing sequence.
- The quadratic-variation formula, from the $L^2$ isometry applied to stopped integrals, and the stopping identity.
- Consistency with the localized Brownian integral when $M=B$.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren 293, Springer (1999), <https://link.springer.com/book/10.1007/978-3-662-06400-9> (stochastic integration with respect to continuous local martingales).
