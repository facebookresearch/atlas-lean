# Neighborhood-based clock statistic

Let a biallelic variant be observed on phased haplotypes at low derived-allele count. Scanning outward from the variant on each side along the haplotypes that carry the derived allele, stop at the first position that is either a *fully linked rarer variant* — a variant carried by a strict subset of those haplotypes — or a *detectable recombination event*, declared by the four-gamete test. Let $d_{-}$ and $d_{+}$ be the physical distances from the focal variant to those two stopping points. The **neighborhood-based clock** statistic is

$$\mathrm{NC} = \log_{10}\bigl( d_{-} + d_{+} \bigr).$$

Larger $\mathrm{NC}$ indicates a younger allele: a rarer variant lying strictly inside the carrier set must have arisen by mutation after the focal variant, and a detectable recombination event on a carrier haplotype must have occurred after it as well, so both stopping points are events that accumulate with the allele's age and with the time it has spent at appreciable frequency. The statistic is computed separately within each derived-allele-count class, so that comparisons between functional classes of variants are made at matched frequency.

Applied this way, $\mathrm{NC}$ is a test for the Maruyama effect: under a constant-size diffusion model with genic selection and no dominance, the mean age and the sojourn-time density of an allele at a given frequency are symmetric in the sign of the selection coefficient, so deleterious alleles at a given frequency are on average younger than neutral alleles at that frequency, and the $\mathrm{NC}$ distributions of the two classes should differ even though their frequencies do not.

## Depends on

- [Four-gamete condition for two sites](../../coalescent-theory/hudson-kaplan-bound-on-recombination-events/four-gametes.md)
- [Haplotypes carrying an allele at a site](../../coalescent-theory/hudson-kaplan-bound-on-recombination-events/carriers.md)
- [Symmetry of the mean age in the selection coefficient](../../population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-neg.md)
- [The Maruyama effect](../../population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-lt.md)

## Expansion

Matching on allele count is essential, since age and frequency are strongly dependent: all comparisons are within a count class, for instance counts $2$ to $6$ in a sample of fully sequenced trios, where family-based phasing makes rare-variant haplotypes reliable. The statistic deliberately avoids absolute age estimation, which demands a demographic model and a recombination map; it is an ordinal clock, usable to compare classes of variants in the same dataset — synonymous against missense, or missense partitioned by a damage prediction — rather than to date a single mutation. Its power is concentrated on low-frequency derived alleles, because strongly deleterious variants rarely reach high frequency, so the theoretically larger age difference at high frequency cannot be exploited. The symmetry in the sign of the selection coefficient is a property of the constant-size diffusion only: in a growing population the mean ages of deleterious and advantageous alleles of the same frequency differ, and simulations show the deleterious-versus-neutral age gap persists, though attenuated, under recent expansion and under a bottleneck followed by expansion.

## Sources

- A. Kiezun, S. L. Pulit, L. C. Francioli, et al., "Deleterious alleles in the human genome are on average younger than neutral alleles of the same frequency", *PLoS Genetics* 9 (2013), e1003301, <https://doi.org/10.1371/journal.pgen.1003301> (PMC3585140). Results, "Neighborhood-based Clock", and Methods (diffusion treatment of mean age and sojourn times; definition of the NC test statistic).
- T. Maruyama, "The age of an allele in a finite population", *Genetical Research* 23 (1974), 137–143, <https://doi.org/10.1017/S0016672300014750>.
