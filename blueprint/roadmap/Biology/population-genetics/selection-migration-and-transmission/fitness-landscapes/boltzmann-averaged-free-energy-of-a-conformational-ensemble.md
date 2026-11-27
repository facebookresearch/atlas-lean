# Boltzmann-averaged free energy of a conformational ensemble

Let a protein exchange among a finite set of conformations $c$, each with free energy $G_c$, at absolute temperature $T$ ($R$ the gas constant). The statistical weight of $c$ is $w_c = e^{-G_c/RT}$ and its equilibrium frequency is $f_c = w_c/\sum_{c'} w_{c'}$. For a set $X$ of conformations define the Boltzmann-weighted average free energy

$$\langle G_X\rangle = -RT\ln\sum_{m\in X} e^{-G_m/RT}.$$

**Three-conformation model (Morrison, Wheeler and Harms, equations (5)–(10)).** With one active conformation $i$ and inactive conformations $j, k$, the observable equilibrium constant and its free energy are

$$K_{\mathrm{obs}} = \frac{f_i}{f_j + f_k} = \frac{e^{-G_i/RT}}{e^{-G_j/RT} + e^{-G_k/RT}}, \qquad \Delta G_{\mathrm{obs}} = -RT\ln K_{\mathrm{obs}} = G_i - \langle G_{j,k}\rangle.$$

**Two sub-ensembles (equations (17)–(18)).** For disjoint conformation sets $X$ (active) and $Y$ (inactive),

$$\Delta G_{\mathrm{obs}} = \langle G_X\rangle - \langle G_Y\rangle.$$

Elementary properties used for epistasis:

1. *Shift equivariance:* $\langle G_X + a\rangle = \langle G_X\rangle + a$ for a constant $a$ added to every $G_m$, $m \in X$.
2. *Soft minimum:* $\min_{m\in X} G_m - RT\ln|X| \le \langle G_X\rangle \le \min_{m\in X}G_m$.
3. *Gradient:* $\partial\langle G_X\rangle/\partial G_m = f_m/\sum_{m'\in X} f_{m'}$, the conditional population of $m$ within $X$.

The frequencies are coupled: lowering $G_j$ lowers $f_i$ even when $G_i$ is unchanged.

## Depends on

- [Boltzmann probability of a state](../../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/boltzmann-prob.md)

## Expansion

$\ln K_{\mathrm{obs}}$ puts the multiplicative equilibrium constant on an additive free-energy scale: $-RT\ln$ of the numerator is $G_i$, and of the denominator is $\langle G_{j,k}\rangle$. Property 1 is immediate from factoring $e^{-a/RT}$ out of the sum; property 2 bounds the sum between its largest term and $|X|$ times it; property 3 is direct differentiation. On this scale mutational effects would add if each conformation's energy shifted additively and the ensemble did not reweight, which is what makes the scale the natural one for measuring epistasis.

## Sources

- A. M. Morrison, L. C. Wheeler and M. J. Harms, *Ensemble epistasis: thermodynamic origins of nonadditivity between mutations*, Genetics 219 (2021), iyab105. <https://doi.org/10.1093/genetics/iyab105>. PMCID: PMC8633102. Equations (5)–(10), (17) and (18).
