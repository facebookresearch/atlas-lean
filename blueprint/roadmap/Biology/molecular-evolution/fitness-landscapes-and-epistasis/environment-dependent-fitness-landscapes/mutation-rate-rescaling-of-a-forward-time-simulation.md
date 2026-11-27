# Mutation-rate rescaling of a forward-time simulation

**Statement** (Ogbunugafor et al. 2016, eq. (3)). In a forward-time Wright–Fisher simulation of a population of effective size $N_e$ with per-site per-generation mutation rate $\mu$, dividing the population size by a factor $m > 1$ and multiplying every rate by the same factor leaves the population-scaled mutation parameter unchanged,

$$N_e \mu = \frac{N_e}{m}\,(\mu m),$$

so a simulation of $N_e/m$ individuals with mutation rate $\mu m$ has the same expected number of new mutations per generation as the original. The same rescaling is applied to the selection coefficients, so the scaled parameters $N_e \mu$ and $N_e s$ are both preserved.

## Depends on

- [Wright–Fisher diffusion limit, generator form](../../../population-genetics/diffusion-theory/diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md)
- [Generator of the Wright–Fisher diffusion with selection and mutation](../../../population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-generator.md)

## Expansion

The diffusion limit of the Wright–Fisher model depends on the parameters only through the products $N_e \mu$ and $N_e s$, with time measured in units of $N_e$ generations, so two parameter sets with the same products describe the same process up to a time rescaling by $m$: the smaller population reaches the same states in $1/m$ as many generations, which is what makes the rescaled simulation cheaper. The approximation fails when the rescaled rates leave the regime where the diffusion applies, that is when $\mu m$ ceases to be small so that multiple mutations per site per generation become common, or when $N_e/m$ is small enough that events of order $1/N_e$ matter; in the reported use, $m = 10^3$ with $N_e = 10^4$ and per-site rates from a normalized mutation matrix for the parasite kept the qualitative dynamics of the unscaled runs.

## Sources

- C. B. Ogbunugafor, C. S. Wylie, I. Diakite, D. M. Weinreich and D. L. Hartl, "Adaptive landscape by environment interactions dictate evolutionary dynamics in models of drug resistance", PLoS Computational Biology 12 (2016), e1004710, Methods ("Simulations of evolution across drug environments"), eq. (3), <https://doi.org/10.1371/journal.pcbi.1004710>, PMCID PMC4726534.
