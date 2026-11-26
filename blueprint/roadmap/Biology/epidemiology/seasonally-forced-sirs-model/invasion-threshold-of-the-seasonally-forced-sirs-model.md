# Invasion threshold of the seasonally forced SIRS model

In the [seasonally forced SIRS model](seasonally-forced-sirs-model-with-vital-dynamics.md) with 1-periodic $\beta(t) = b_0\bigl(1 + b_1\cos(2\pi t - \phi)\bigr)$, linearize at the disease-free state $(S, I, R) = (N, 0, 0)$. The infectious class then satisfies

$$\dot I = \bigl(\beta(t) - (\nu + \mu)\bigr) I,$$

so over one period $I$ is multiplied by the Floquet factor

$$\exp\!\left(\int_0^1 \beta(t)\,dt - (\nu+\mu)\right) = \exp\bigl(b_0 - (\nu+\mu)\bigr).$$

The disease-free periodic state is therefore linearly unstable to invasion if and only if

$$\mathcal{R}_0 = \frac{\bar\beta}{\nu+\mu} = \frac{b_0}{\nu+\mu} > 1, \qquad \bar\beta = \int_0^1 \beta(t)\,dt = b_0,$$

and linearly stable if $\mathcal{R}_0 < 1$. The amplitude $b_1$ and phase $\phi$ do not affect the threshold, although they shape the epidemics that follow invasion.

## Depends on

- [Seasonally forced SIRS model with vital dynamics](seasonally-forced-sirs-model-with-vital-dynamics.md)

## Proof depends on

- [Variation of constants for time-varying linear systems](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/variation-of-parameters-time-varying.md)

## Expansion

At $I = 0$, $R = 0$ and $S = N$ the $S$ and $R$ equations are at rest. To first order in $I$, the infection term is $\beta(t)I$ and the outflow is $(\nu+\mu)I$, which gives a scalar linear periodic equation. Its solution is $I(t) = I(0)\exp\int_0^t(\beta - \nu - \mu)$. Since $\int_0^1\cos(2\pi t - \phi)\,dt = 0$, the growth over a period depends only on the mean transmission rate. With a single infected compartment, the basic reproduction number of the periodic model is the time-averaged transmission rate divided by the exit rate. With several infected classes, for example latent stages, the mean-over-period formula no longer holds in general, and the threshold must be computed from the Floquet spectrum of the linearized periodic system.

## Sources

- J. C. Lang, *Use of mathematical modelling to assess respiratory syncytial virus epidemiology and interventions: a literature review*, Journal of Mathematical Biology 84 (2022), 26, <https://doi.org/10.1007/s00285-021-01706-y>, PMCID PMC8882104. Seasonal transmission rate Eq. (1) and SIRS structure.
