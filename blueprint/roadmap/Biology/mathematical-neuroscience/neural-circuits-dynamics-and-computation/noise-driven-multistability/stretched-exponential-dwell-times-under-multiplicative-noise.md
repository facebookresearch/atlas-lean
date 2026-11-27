# Stretched-exponential dwell times under multiplicative noise

**Setting.** Add noise to the [quintic Hopf amplitude equation](quintic-normal-form-of-the-hopf-bifurcation.md) in its bistable window $-\lambda^2/4 < \beta < 0$, $\lambda > 0$:

$$dr = (-r^5 + \lambda r^3 + \beta r)\,dt + \sigma\big(\eta_a\, dW_1 + \eta_m\, r\, dW_2\big),$$

where $W_1, W_2$ are independent Wiener processes, the first term is additive (state-independent) noise and the second multiplicative (state-dependent) noise whose amplitude grows with $r$. The **dwell time** in a mode is the time between successive crossings of the separatrix $r_-$.

**Definitions.** A dwell-time distribution is a **stretched exponential** if its survival function is

$$\Pr(D > x) = \exp(-a x^b), \qquad a > 0,\ 0 < b \le 1,$$

a Weibull law; $b = 1$ is the memoryless exponential law of a Poisson switching process. Its hazard rate is $h(x) = a b\, x^{b-1}$, and $\log(-\log \Pr(D > x)) = \log a + b \log x$, so $a$ and $b$ can be estimated by linear regression of the empirical survival function in $\log x$–$\log(-\log P)$ coordinates.

**Properties.**

1. For $0 < b < 1$ the hazard $h(x)$ is strictly decreasing: the longer the system has stayed in a mode, the less likely it is to leave it per unit time (trapping), and the distribution has a heavier right tail than any exponential with the same median.
2. With purely additive noise, fluctuations in the high-amplitude mode have the same standard deviation as in the low-amplitude mode, so the standard deviation does not scale with the mean amplitude; adding the multiplicative term makes the standard deviation grow in proportion to the mean, as in scale-invariant (proportional) fluctuations.
3. Purely multiplicative noise ($\eta_a = 0$) vanishes at the stable focus $r = 0$, so once the trajectory approaches the origin it is quenched and never switches back; a positive additive component is necessary for sustained switching.

## Depends on

- [Quintic normal form of the Hopf bifurcation and its bistable window](quintic-normal-form-of-the-hopf-bifurcation.md)

## Expansion

The hazard of a Weibull law is $h = -\frac{d}{dx}\log\Pr(D > x) = abx^{b-1}$, decreasing iff $b < 1$; the double-log linearization is immediate. With multiplicative noise the effective noise intensity depends on where in the basin the trajectory sits: just after entering the low-amplitude basin the noise is still large and a quick return is likely, but trajectories that drift toward the origin experience weaker noise and become less likely to escape, which yields a decreasing hazard; symmetrically, trajectories deep in the high-amplitude basin experience large noise that keeps them there. Simulations of the stochastic normal form with both noise terms reproduce bimodal power distributions with proportional scaling and stretched-exponential dwell times with $b < 1$, matching human resting EEG, whereas purely additive noise or slow noise on the bifurcation parameter (a supercritical alternative) does not.

## Sources

- Freyer F, Roberts JA, Ritter P, Breakspear M, "A canonical model of multistability and scale-invariance in biological systems" (2012), Results, "Switching with purely additive noise" and "The role of multiplicative (state dependent) noise" (Equations (3)–(4)), and Materials and Methods, "Parameter estimates for stretched exponential dwell time CDFs", <https://doi.org/10.1371/journal.pcbi.1002634>, PMCID PMC3415415.
