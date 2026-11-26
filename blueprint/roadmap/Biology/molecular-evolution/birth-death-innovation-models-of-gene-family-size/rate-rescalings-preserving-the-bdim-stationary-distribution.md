# Rate rescalings that preserve the BDIM stationary distribution

**Statement.** Let a [birth–death–innovation model](stationary-family-size-distribution-of-a-bdim.md) on $\{0,\dots,N\}$ have birth rates $\lambda_i$ and death rates $\delta_i$, and let $g:\{0,\dots,N\}\to(0,\infty)$ with $g(0) = 1$. The transformed model
$$\lambda^*_i = \lambda_i\,g(i),\qquad \delta^*_i = \delta_i\,g(i-1)$$
has the same stationary family-size distribution as the original, although its transient dynamics, including mean extinction and formation times, can be very different. In particular, starting from a linear BDIM, $g(i) = (i+1)^{d-1}$ gives rational BDIMs of degree $d$ and $g(i) = (i+1)^{d-1}\big(1 - i/(N+c)\big)$ gives logistic-type BDIMs, all with the linear model's stationary distribution.

## Expansion

The stationary distribution depends only on the ratios $\chi(i) = \lambda_{i-1}/\delta_i$, and $\lambda^*_{i-1}/\delta^*_i = \lambda_{i-1}g(i-1)/(\delta_i g(i-1)) = \chi(i)$. The rescaling multiplies both exit rates from state $i-1$ toward $i$ and from $i$ toward $i-1$ consistently, changing the holding times but not the balance of flows. Hence fitting the observed family-size distribution cannot distinguish these models; the authors use this freedom to show that the mean time to form the largest observed families is minimized by a nonlinear rational BDIM of degree about $2.7$, and is still far longer than any realistic evolutionary timescale.

## Sources

- Karev GP, Wolf YI, Berezovskaya FS, Koonin EV, "Gene family evolution: an in-depth theoretical and simulation analysis of non-linear birth-death-innovation models", BMC Evol Biol (2004), Section 2, "Non-linear transformation of BDIM", Eq. (2.4), <https://doi.org/10.1186/1471-2148-4-32>, PMCID PMC523855.
