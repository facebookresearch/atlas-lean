# The mutational load with epistatic gene interactions

For deleterious mutations at many loci, the Haldane–Muller theorem of mutation–selection balance says that the load depends only on the whole-genome deleterious mutation rate $U$, not on the selection coefficients: relative to an ideal genotype of fitness $1$, the mean population fitness is $e^{-U}$ (Genetic load, Wikipedia, section Segregating deleterious mutations). Negative epistasis can make the purging of deleterious mutations more efficient, by making the variance in fitness larger than expected from the variance in the number of deleterious mutations, and truncation selection, in which for example the $10\%$ of individuals with the most deleterious mutations fail to reproduce, is its most extreme form under soft selection; Wikipedia cites Crow and Kimura (1979) and Kimura and Maruyama (1966) for these statements. The single-locus Haldane–Muller load $2U - U^2$ of a diploid locus with multiplicative fitnesses is a separate, one-locus calculation. Under multiplicative fitnesses across loci the genome-wide value follows from it (derivation): if loci $k$ contribute independent factors $1 - L_k$ with $L_k \approx 2u_k$ for small per-locus rates $u_k$, the mean fitness is $\prod_k(1 - L_k) \approx \exp(-\sum_k2u_k) = e^{-U}$ with $U = \sum_k2u_k$ the diploid genomic rate.

## Depends on

- [Haldane–Muller load](../../../Biology/population-genetics/mutation-selection-balance/load-mult-at-equilibrium.md)

## Expansion

1. The multilocus model: per-locus mutation rates, a fitness function of the number of deleterious mutations, and the recombination and population assumptions.
2. Multiplicative fitness across loci and the mean fitness $e^{-U}$, from the single-locus load.
3. The equilibrium distribution of the number of mutations per individual under the model's assumptions, and the load under epistatic fitness functions.
4. Truncation selection as the extreme of negative epistasis, and the comparison of its load with the multiplicative case.

## Sources

- Genetic load, Wikipedia, section Segregating deleterious mutations. <https://en.wikipedia.org/wiki/Genetic_load>
- Original result: M. Kimura and T. Maruyama, The mutational load with epistatic gene interactions in fitness, Genetics 54 (1966), 1337–1351. <https://doi.org/10.1093/genetics/54.6.1337> The statement on epistasis follows the Wikipedia account.
- Original result: J. F. Crow and M. Kimura, Efficiency of truncation selection, Proc. Natl. Acad. Sci. USA 76 (1979), 396–399. <https://doi.org/10.1073/pnas.76.1.396> The statement on truncation selection follows the Wikipedia account.
