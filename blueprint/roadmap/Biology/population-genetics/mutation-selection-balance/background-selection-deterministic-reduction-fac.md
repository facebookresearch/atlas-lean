# Background selection reduces the effective size to the mutation-free class

At the [Poisson equilibrium of multiplicative mutation–selection balance](multilocus-multiplicative-mutation-selection-poi.md) with genome-wide mutation rate $U$ and selection
coefficient $s$, in an asexual haploid population (a non-recombining genome), the class carrying no deleterious mutation has frequency exactly

$$f_0 = e^{-U/s}.$$

Under the approximation that, in a non-recombining region, the neutral genealogy is that of the mutation-free class alone,
because every other class descends from it within a few multiples of $1/s$ generations, and when selection is strong relative to drift in that class ($N s e^{-U/s} \gg 1$), the effective population size for
linked neutral variation is

$$N_e \approx N e^{-U/s}.$$

The first statement is exact; the second is an approximation, and neither diploid selection with heterozygous effects
nor the effect of recombination, which weakens it, is covered here.

## Depends on

- [Poisson equilibrium of multiplicative mutation–selection balance](multilocus-multiplicative-mutation-selection-poi.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VIII.8, p. 398, "Background selection" (for tightly linked loci, approximately a reduction of the effective population size to the fraction of mutation-free haplotypes, after Charlesworth (1994)).
