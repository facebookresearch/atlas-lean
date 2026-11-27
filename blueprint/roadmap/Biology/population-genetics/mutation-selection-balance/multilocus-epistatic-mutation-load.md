# The mutational load with epistatic gene interactions

For deleterious mutations at many loci, the Haldane–Muller principle of mutation–selection balance (Haldane 1937; Muller 1950) says that the load is largely independent of the harmfulness of the mutant, and for loci independent in their effect the total fitness relative to a population with mutation rate zero is $\prod_k(1 - L_k) \approx e^{-\sum_kL_k}$, with $L_k$ the load at locus $k$ (Kimura, Maruyama and Crow 1963, equation (8)). The single-locus Haldane–Muller load $2U - U^2$ of a diploid locus with multiplicative fitnesses is a separate, one-locus calculation. Under multiplicative fitnesses across loci the genome-wide value follows from it (derivation): if loci $k$ contribute independent factors $1 - L_k$ with $L_k \approx 2u_k$ for small per-locus rates $u_k$, the mean fitness is $\prod_k(1 - L_k) \approx \exp(-\sum_k2u_k) = e^{-U}$ with $U = \sum_k2u_k$ the diploid genomic rate, independent of the selection coefficients. Epistasis changes this: for a fitness that decreases as a quadratic function of the number of mutant genes in an individual, in a large population with free recombination, Kimura and Maruyama (1966, equation (1.14)) find a load roughly equal to the mutation rate $M$ per gamete when the quadratic term dominates the linear one, against $2M/(1 + 2M)$, roughly the total rate $2M$ per zygote, without epistasis. Truncation selection is the most efficient form of directional selection, and for mutations affecting viability in Drosophila, truncation selection or reasonable departures from it can reduce the mutation load greatly (Crow and Kimura 1979).

## Depends on

- [Haldane–Muller load](../../../Biology/population-genetics/mutation-selection-balance/load-mult-at-equilibrium.md)

## Expansion

1. The multilocus model: per-locus mutation rates, a fitness function of the number of deleterious mutations, and the recombination and population assumptions.
2. Multiplicative fitness across loci and the mean fitness $e^{-U}$, from the single-locus load.
3. The equilibrium distribution of the number of mutations per individual under the model's assumptions, and the load under the quadratic fitness function of Kimura and Maruyama; for multiplicative fitness in an asexual haploid population see the [Poisson equilibrium of multiplicative mutation–selection balance](multilocus-multiplicative-mutation-selection-poi.md).
4. Truncation selection, and the comparison of its load with the multiplicative case.

## Sources

- J. B. S. Haldane, The effect of variation on fitness, Amer. Nat. 71 (1937), 337–349.
- H. J. Muller, Our load of mutations, Amer. J. Hum. Genet. 2 (1950), 111–176.
- M. Kimura, T. Maruyama and J. F. Crow, The mutation load in small populations, Genetics 48 (1963), 1303–1312, introduction and equation (8). <https://doi.org/10.1093/genetics/48.10.1303>
- Original result: M. Kimura and T. Maruyama, The mutational load with epistatic gene interactions in fitness, Genetics 54 (1966), 1337–1351, Section 1, equation (1.14). <https://doi.org/10.1093/genetics/54.6.1337>
- Original result: J. F. Crow and M. Kimura, Efficiency of truncation selection, Proc. Natl. Acad. Sci. USA 76 (1979), 396–399, abstract. <https://doi.org/10.1073/pnas.76.1.396>
