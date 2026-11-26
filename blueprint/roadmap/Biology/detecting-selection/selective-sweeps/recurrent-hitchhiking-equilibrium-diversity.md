# Equilibrium neutral diversity under recurrent selective sweeps

Assume strongly beneficial substitutions ($N_e s \gg 1$) occur along the genome as a time-homogeneous Poisson process at rate $\nu$ per site per generation, each one a deterministic sweep with selection coefficient $s$ completed so fast that sweeps do not overlap. A focal neutral site recombines with selected sites at rate $\rho$ per nucleotide per generation, uniform along the chromosome. Let $\alpha = 2N_e s$ and let $\pi_0$ be the neutral equilibrium nucleotide diversity. Then the equilibrium diversity at the focal site is approximately

$$\pi = \pi_0\,\frac{\rho}{\rho + \kappa\,\alpha\,\nu}, \tag{1}$$

with a constant $\kappa \approx 0.075$ obtained from the single-sweep reduction integrated over the distance to the selected sites.

**Consequences.** The ratio $\pi/\pi_0$ depends on the sweep parameters only through the product $\alpha\nu$. Rare strong sweeps and frequent weak ones therefore predict the same mean diversity, and only the variance of diversity along the genome separates them. Diversity increases with recombination rate in a saturating way, $\pi/\pi_0 \to 1$ as $\rho \to \infty$ and $\pi \approx \pi_0\rho/(\kappa\alpha\nu)$ for $\rho \ll \kappa\alpha\nu$.

## Proof sketch

Heterozygosity at the focal site relaxes toward $\pi_0$ at rate $1/(2N_e)$ per generation by drift and mutation. A sweep at map distance $c$ multiplies it by a factor $1 - D(c/s)$, where $D$ is the probability that the focal lineage stays linked to the beneficial allele throughout the sweep. $D$ decays from $1$ at $c = 0$ to $0$ once $c$ is a few times $s/\ln(2N_e s)$. Sweeps hitting the region within map distance $c$ arrive at total rate proportional to $\nu c/\rho$ per generation. The expected loss per generation is therefore $\pi\cdot(\nu/\rho)\int D(c/s)\,dc \propto \pi\,\nu s/\rho$. Balancing this against the recovery $(\pi_0 - \pi)/(2N_e)$ gives $\pi_0 - \pi = \pi\,\kappa\,2N_e s\,\nu/\rho$, which is (1). The numerical constant $\kappa$ comes from evaluating the integral of the hitchhiking reduction. The model ignores interference between simultaneous sweeps, which slightly weakens hitchhiking mainly in low-recombination regions, and it predicts no lasting excess of high-frequency derived alleles in the site frequency spectrum.

## Proof depends on

- [Probability that a neutral lineage stays linked during a deterministic sweep](hitchhiking-deterministic-escape-probability.md)

## Sources

- W. Stephan, "Selective sweeps", Genetics 211 (2019), 5–13, section "Selective Sweeps at Multiple Loci: Recurrent selective sweeps", Equation (1) (after T. Wiehe and W. Stephan, 1993), <https://doi.org/10.1534/genetics.118.301319>, PMCID PMC6325696.
