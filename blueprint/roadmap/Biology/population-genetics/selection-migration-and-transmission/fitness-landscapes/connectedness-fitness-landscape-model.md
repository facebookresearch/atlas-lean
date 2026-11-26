# Connectedness fitness landscape model

In the **connectedness (CN) model** each locus $i$ of $\ell$ loci takes part in a fraction $\mu_i \in [0,1]$ of independent "pathways", and all loci in a pathway interact epistatically, so a set of loci $i, j, k, \dots$ interacts with probability proportional to $\mu_i \mu_j \mu_k \cdots$ (the chance that they share a pathway). The [variance fraction](global-epistasis-from-widespread-epistasis.md) of locus $i$ is

$$v_i = \frac{\mu_i}{1 + \mu_i} \quad (\ell \text{ large}), \qquad v_i = \frac{\mu_i}{\bar\mu\, \ell} \quad (\ell \text{ small}),$$

with $\bar\mu$ the mean of $\mu$ over loci, so the distribution of $\mu$ across loci determines the distribution of variance fractions, which is invariant during adaptation.

Properties:

1. The CN model is a generalized NK model and is equivalent to a Gaussian fitness landscape with exponentially decaying correlations; its ruggedness is tuned by $\bar\mu$, from additive to maximally epistatic. At $\mu_i = 1$ for all $i$, $v_i = 1/2$, and by the global-epistasis law the fitness after a mutation is independent of the fitness before it, as in the House-of-Cards model.
2. Fitness effects are **memoryless**: the effect of a new mutation depends on the evolutionary history only through the current fitness. In general this requires the epistasis between the $(k+1)$-th mutation and the $k$ previous ones to satisfy $e_{k+1,1:k} = v_{k+1} v_{1:k}$, with $v_{1:k}$ the combined variance fraction of the previous mutations; the CN model satisfies it.
3. In the well-adapted regime (normalized fitness $z = (y - \bar y)/\sqrt{V}$ large, effects $\sigma = s/\sqrt{V}$), the distribution of fitness effects satisfies $\rho(\sigma \mid z)/\rho(-\sigma \mid z) = e^{-\sigma z}$ for $\sigma > 0$, so beneficial effects are exponentially distributed whatever the distribution of variance fractions (unless it is singular). Under strong-selection weak-mutation dynamics, mean fitness then grows as $z \sim t^{1/5}$ and the number of fixed beneficial mutations as $n_s \sim t^{2/5}$.

## Depends on

- [Global epistasis from widespread epistasis](global-epistasis-from-widespread-epistasis.md)

## Expansion

A locus has a large variance fraction because it participates in many pathways, not because it perturbs a few pathways strongly. Unlike regular landscapes, where every locus has the same variance fraction, the CN model allows heterogeneous $v_i$; the declining supply of high-$v$ beneficial loci as fitness increases, combined with diminishing returns, produces the decelerating power laws. Writing $\sigma = -2vz + 2\sqrt{v}\,\nu$ with $\nu$ standard normal and $v \ll 1$, Laplace's method shows that an effect $\sigma$ at large $z$ comes mainly from loci with $v \approx |\sigma|/(2z)$, giving $\rho(\sigma \mid z) \approx (2z)^{-1} P(|\sigma|/2z)\, e^{-z(\sigma + |\sigma|)/2}$. Hence the beneficial rate is $U_b \sim z^{-2}$ (when the variance-fraction density is positive near $0$) and the typical beneficial effect is $\sigma \sim z^{-1}$; under SSWM $p_{\mathrm{fix}} \sim \sigma$, so $dz/dt \sim U_b p_{\mathrm{fix}} \sigma \sim z^{-4}$ and $dn_s/dt \sim U_b p_{\mathrm{fix}} \sim z^{-3}$, which integrate to the two power laws. For homogeneous loci ($P(v) = \delta(v - \bar v)$) the DFE is instead Gaussian with mean $-2\bar v z$ and fitness plateaus near $z \approx \bar v^{-1/2}$. A modular alternative, in which each locus interacts only within one module and overall fitness is a function of module fitnesses, does not in general give memoryless effects. Derivations of $v_i$ and of memorylessness are in the paper's appendices.

## Sources

- G. Reddy and M. M. Desai, "Global epistasis emerges from a generic model of a complex trait", eLife 10 (2021), e64740, Results ("The connectedness model", Equation 12, Figure 4) and Appendix 3 (Equations 100–122), <https://doi.org/10.7554/eLife.64740>, PMCID: PMC8057814.
