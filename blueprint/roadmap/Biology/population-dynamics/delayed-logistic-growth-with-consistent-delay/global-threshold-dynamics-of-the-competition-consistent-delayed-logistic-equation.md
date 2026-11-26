# Global threshold dynamics of the competition-consistent delayed logistic equation

**Model.** Start from the logistic equation $x' = \gamma x - \mu x - \kappa x^2$ with birth rate $\gamma > 0$, death rate $\mu > 0$ and intraspecific competition $\kappa > 0$, and let recruitment at time $t$ come from individuals born at $t - \tau$ ($\tau > 0$) that survive to maturity. If maturing individuals die at rate $\mu$ and compete with the *whole* population $x$ (juveniles and adults share the environment), the fraction of a cohort surviving from $t - \tau$ to $t$ is $\exp\big(-\mu\tau - \kappa\int_{t-\tau}^t x(v)\,dv\big)$, which gives

$$x'(t) = \gamma\, x(t-\tau)\exp\Big(-\mu\tau - \kappa\int_{t-\tau}^{t} x(v)\,dv\Big) - \mu x(t) - \kappa x(t)^2,$$

with positive continuous initial data on $[-\tau, 0]$. The decline terms of the delayed growth are consistent with the instantaneous decline $-\mu x - \kappa x^2$ of the model itself. Define

$$\mathcal{R}_0 = \frac{\gamma e^{-\mu\tau}}{\mu}.$$

A positive equilibrium $x^*$ exists iff $\mathcal{R}_0 > 1$, and then it is unique: it is the root of $\gamma e^{-\mu\tau - \kappa\tau x} = \mu + \kappa x$.

**Theorem.**

1. If $\mathcal{R}_0 \le 1$, then $0$ attracts all nonnegative solutions; if $\mathcal{R}_0 < 1$, $0$ is globally asymptotically stable.
2. If $\mathcal{R}_0 > 1$, the positive equilibrium $x^*$ is globally asymptotically stable for positive initial data.

In particular, unlike Hutchinson's delayed logistic equation, no delay produces sustained oscillations; a longer maturation delay only lowers $\mathcal{R}_0$ and, past $\tau_H = \ln(\gamma/\mu)/\mu$, drives the population extinct.

## Expansion

At a positive equilibrium the per-capita recruitment $\gamma e^{-\mu\tau - \kappa\tau x}$ is decreasing and the per-capita loss $\mu + \kappa x$ increasing in $x$, so they cross once iff $\gamma e^{-\mu\tau} > \mu$. Local stability comes from the characteristic equation; global attractivity uses the comparison theorem for cooperative delay differential equations to trap solutions between upper and lower solutions, and the theory of chain transitive sets to rule out limit sets other than equilibria. For two competing species with this structure, the extinction of species $i$ whenever $\mathcal{R}_0^{(i)} \le 1$ carries over, and an adaptive-dynamics analysis shows that with identical parameters except the delay, a mutant with a shorter delay invades, so selection pushes the delay down unless growth rate and delay are positively correlated.

## Sources

- C.-J. Lin, T.-H. Hsu and G. S. K. Wolkowicz, "Population Growth and Competition Models with Decay and Competition Consistent Delay", arXiv:2106.08205 (2021), Section 2 (derivation, definition of $\mathcal{R}_0$, Lemma 1 and Theorem 1), Section 3 (Theorem 2, Corollary 1, Results 1–2), <https://doi.org/10.48550/arXiv.2106.08205>.
