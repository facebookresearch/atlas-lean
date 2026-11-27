# Tumour growth rate with surface-growing microlesions

In the one-type [microlesion seeding model](microlesion-seeding-model-and-its-euler-lotka-growth-rate.md), let each lesion be a ball whose radius grows at speed $v$ (cells per unit time) with replication only on its surface, so $V(a) = \tfrac{4\pi}{3}(va)^3$, and let a fraction $M$ of surface cells escape to found new lesions, so

$$\phi(a) = M\,V'(a) = 4\pi M v^3 a^2, \qquad \tilde\phi(s) = \frac{8\pi M v^3}{s^3} .$$

Then the Euler–Lotka root is

$$G = (8\pi M)^{1/3}\,v,$$

and the expected number of lesions is exactly

$$N(t) = \frac13\Big(e^{Gt} + 2\,e^{-Gt/2}\cos\big(\tfrac{\sqrt3}{2}Gt\big)\Big),$$

with $N(0) = 1$ and $N(t) \sim e^{Gt}/3$. Although every lesion grows only polynomially (volume $\propto a^3$), the tumour as a whole grows exponentially with rate $G$; for example $M = 10^{-6}$ and $v = 0.1$ cells per day suffice to reach a clinically detectable size within years.

**Slowing lesions.** If surface growth slows as $e^{-\lambda a}$, so that $V'(a) = 4\pi v^3a^2e^{-\lambda a}$ and each lesion saturates at $V(\infty) = 8\pi v^3/\lambda^3$, then $\tilde\phi(s) = 8\pi M v^3/(s+\lambda)^3$ and $G = (8\pi M)^{1/3}v - \lambda$: the tumour still grows exponentially if and only if migration is strong enough that $(8\pi M)^{1/3}v > \lambda$.

**New drivers.** With driver-dependent speeds $v_n = n v_1$ and a neutral mutant-sector fraction governed by a mutation rate $\mu$, the type-1 lesions grow at rate $G_1 = (8\pi M)^{1/3}v_1 - \mu$, which can be negative even though the total cell number keeps increasing, because cells convert to higher driver types.

## Depends on

- [Microlesion seeding model and its Euler–Lotka growth rate](microlesion-seeding-model-and-its-euler-lotka-growth-rate.md)

## Proof sketch

The Euler–Lotka equation $\tilde\phi(G) = 8\pi M v^3/G^3 = 1$ has the single real root $G = (8\pi M)^{1/3}v$. With $\tilde F = \tilde\phi/(1 - \tilde\phi) = G^3/(s^3 - G^3)$, the Laplace transform of $N(t) = 1 + \int_0^t F$ is $\tilde N(s) = \frac1s(1 + \tilde F) = s^2/(s^3 - G^3) = \frac13\sum_{\omega^3 = 1}\frac{1}{s - \omega G}$, and inverting over the three cube roots of unity gives the formula for $N(t)$. The slowing case replaces $s$ by $s + \lambda$ in $\tilde\phi$, shifting the root by $-\lambda$. For volumetric growth, where every cell divides at rate $b$, the source finds that the tumour grows at the cell birth rate, $G = b$; the spatial constraint of surface growth is what makes migration, not division, set the tumour's growth rate (Results, "Only one driver" and "Multiple driver mutations", of the source).

## Sources

- C. Paterson, M. A. Nowak, B. Waclaw, "An exactly solvable, spatial model of mutation accumulation in cancer", Scientific Reports (2016), <https://doi.org/10.1038/srep39511> (PMC5177951).
