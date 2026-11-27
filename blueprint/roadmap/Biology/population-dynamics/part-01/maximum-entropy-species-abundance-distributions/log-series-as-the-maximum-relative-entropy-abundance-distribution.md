# Log-series as the maximum relative entropy abundance distribution

**Setting.** Let $P(n)$, $n = 1,2,\dots$, be the species abundance distribution: the probability that a species present in the community has $n$ individuals. Given a prior $P_\pi(n)$, the relative entropy of $P$ is

$$\Delta H[P] = -\sum_{n \ge 1} P(n)\log\frac{P(n)}{P_\pi(n)} .$$

Constraints have the form $\sum_n P(n)\,h_j(n) = z_j$ for $j = 0,\dots,J-1$, with $h_0 \equiv 1$, $z_0 = 1$ (normalization).

**Maximum relative entropy.** The maximizer of $\Delta H$ under these constraints is the Gibbs form

$$P(n) = P_\pi(n)\exp\Big(-\sum_{j}\lambda_j h_j(n)\Big),$$

with Lagrange multipliers $\lambda_j$ fixed by the constraints.

**Scale-invariant prior.** If organisms are randomly placed (more generally, if each species' abundance in a subarea is negative binomial with any clumping parameter), the only abundance distribution that is unchanged by changing the sampled area, and thus carries no information about spatial scale, is

$$P_\pi(n) \propto \frac{1}{n},$$

the discrete Jeffreys prior, uniform in $\log n$.

**Theorem (log-series).** With $P_\pi(n) \propto 1/n$ and the two constraints $h_0 = 1$ and $h_1(n) = n$ (fixed mean abundance $\bar n > 1$), the maximum relative entropy SAD is Fisher's log-series

$$P(n) = \phi\,\frac{\omega^n}{n}, \qquad 0 < \omega < 1, \quad \phi = \frac{-1}{\log(1-\omega)},$$

where $\omega = e^{-\lambda_1}$ is determined by $\bar n = \dfrac{-\omega}{(1-\omega)\log(1-\omega)}$.

## Expansion

Treating each of $S$ species as completely idiosyncratic makes the community-level abundance vector a product of independent identically distributed draws, so the counts $s_n$ of species with abundance $n$ are multinomial; maximizing that multinomial probability with Stirling's approximation is maximizing $\Delta H$. Substituting $P_\pi \propto 1/n$ and $h_1 = n$ into the Gibbs form gives $P(n) \propto e^{-\lambda_1 n}/n$, and normalization gives $\phi$ via $\sum_{n\ge1}\omega^n/n = -\log(1-\omega)$. Adding $h_2(n) = \log n$ gives $P(n) \propto n^{-1-\lambda_2}e^{-\lambda_1 n}$, and adding both $\log n$ and $(\log n)^2$ gives a discretized log-normal-type tail. The log-series is thus reached without the demographic assumptions of neutral theory, as the least informative SAD consistent with a fixed mean.

## Sources

- S. Pueyo, F. He, T. Zillio, "The maximum entropy formalism and the idiosyncratic theory of biodiversity", Ecology Letters 10(11) (2007) 1017–1028, Eqs. (7)–(16) and Appendix B, <https://doi.org/10.1111/j.1461-0248.2007.01096.x>, PMCID PMC2121135.
