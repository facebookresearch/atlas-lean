# Alternative definitions of allele age

The age of an allele observed at frequency $x$ depends on what is counted. Maruyama and Kimura (1975, abstract) compute the mean age of a mutant at frequency $x$ in two versions, including or excluding the possibility that it had been at frequency $1$ during the process, so that past periods of fixation are either counted or not. Kiezun et al. (2013, Introduction) state the hypotheses under which the classical comparison is exact: Maruyama predicts that deleterious and advantageous alleles are both younger than neutral alleles at the same frequency, with a larger difference for more strongly selected alleles, and under constant population size and no dominance the mean age conditional on frequency is exactly symmetric in the direction of selection. In their diffusion calculations (Results) a neutral allele observed at $x$ spent on average an equal time at each frequency below $x$, whereas a deleterious allele spent progressively less time at higher frequencies, and the difference in mean age comes mainly from shorter sojourns at high frequencies. The constant neutral profile is the rare-origin limit of the conditional sojourn density (derivation): with the neutral Green's function $G(p, z) = 2p/z$ for $p < z$ and $G(z, x) = 2z/x$ for $z < x$, the ratio $G(p, z)G(z, x)/G(p, x)$ equals $2$ for $p < z < x$, in units of $2N$ generations.

## Depends on

- [The Maruyama effect](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-lt.md)
- [Symmetry of the mean age in the selection coefficient](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-neg.md)
- [Maruyama–Kimura conditional sojourn density](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/age-density.md)
- [Neutral Wright–Fisher Green's function](../sojourn-times-of-the-wright-fisher-diffusion/neutral-green.md)

## Expansion

1. The mean age including periods at frequency $1$ and the mean age excluding them, from the Maruyama–Kimura moment formulas, as two statements.
2. The constant neutral sojourn profile below the current frequency, from the neutral Green's function.
3. Dominance, with fitnesses $1$, $1 + hs$, $1 + s$, where the symmetry in the sign of selection need not hold, as a separate statement with its own source.
4. Variable population size, as separate statements with their own sources.

## Sources

- T. Maruyama and M. Kimura, Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604, abstract. <https://doi.org/10.1073/pnas.72.4.1602>
- A. Kiezun et al., Deleterious alleles in the human genome are on average younger than neutral alleles of the same frequency, PLoS Genet. 9 (2013), e1003301, Introduction and Results. <https://doi.org/10.1371/journal.pgen.1003301>
