# Phasing uncertainty

Coalescent hidden Markov methods that take haplotypes as input need phased data, while sequencing gives unphased genotypes, and computationally phased haplotypes contain switch errors. Browning and Browning (2011, Box 2) measure switch error by the number of switches needed to turn the inferred phase of an individual into the true phase, divided by the number of opportunities for a switch, the number of heterozygous markers minus one. Terhorst, Kamm and Song (2017) show by simulation that switch errors at rates of $1\%$ and $5\%$, approximate bounds for existing phasing algorithms, make MSMC estimates of recent population size diverge, by up to four orders of magnitude over the last 3 ky for $n = 4$ (Results and Figure 1). Their method SMC++ uses as observations, at each site, the number $a \in \{0, 1, 2\}$ of derived alleles in one distinguished diploid individual and the number $b$ of derived alleles among the remaining $n - 2$ haplotypes (Online Methods); both counts are unchanged by any permutation of the alleles within individuals, so the likelihood, and hence the estimate, does not depend on phase, and the same holds for methods based on the site-frequency spectrum alone, such as dadi. Phase invariance is thus a property of the observation model, distinct from robustness to switch errors measured in simulation.

## Expansion

1. Genotypes, haplotypes and phase configurations, and the switch-error rate as a measure of phasing accuracy.
2. Invariance under within-individual allele permutations of observations that depend only on derived-allele counts, and its consequence for the likelihood.
3. A likelihood that sums over the phase configurations compatible with the genotypes, and a likelihood with an explicit switch-error channel, as alternatives for haplotype-based methods.
4. The effect of switch errors on haplotype-based estimates of recent population size, as shown by simulation.

## Sources

- J. Terhorst, J. A. Kamm and Y. S. Song, Robust and scalable inference of population history from hundreds of unphased whole genomes, Nat. Genet. 49 (2017; online 2016), 303–309, Results (Figure 1) and Online Methods. <https://doi.org/10.1038/ng.3748>
- S. R. Browning and B. L. Browning, Haplotype phasing: existing methods and new developments, Nat. Rev. Genet. 12 (2011), 703–714, Box 2. <https://doi.org/10.1038/nrg3054>
