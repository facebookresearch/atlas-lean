# The $R_{X/Y}$ statistic and its neutral expectation

Let populations $X$ and $Y$ descend from a common ancestral population and let ancestral states be fixed by an outgroup. At each variable site $i$ of a class of sites (e.g. synonymous or non-synonymous), $d_{Xi}$ of $n_{Xi}$ sampled chromosomes from $X$ carry the derived allele, and similarly $d_{Yi}$ of $n_{Yi}$ from $Y$. Define

$$L_{X\neg Y} = \sum_i \frac{d_{Xi}}{n_{Xi}}\Big(1 - \frac{d_{Yi}}{n_{Yi}}\Big), \qquad R_{X/Y} = \frac{L_{X\neg Y}}{L_{Y\neg X}},$$

the expected number of derived alleles carried by a random chromosome from $X$ but not by a random chromosome from $Y$, divided by the converse. Standard errors are obtained by a weighted block jackknife over contiguous genomic blocks.

**Proposition.** Let $p_{Xi}$, $p_{Yi}$ be the population derived-allele frequencies at site $i$ at sampling time. Then

$$\sum_i \big(p_{Xi}(1 - p_{Yi}) - p_{Yi}(1 - p_{Xi})\big) = \sum_i p_{Xi} - \sum_i p_{Yi},$$

the difference between the expected numbers of derived alleles per chromosome in $X$ and in $Y$. If the sites evolve neutrally, both lineages have the same per-generation mutation rate and the same number of generations since the split, and there is no gene flow from an outside source, then $E[\sum_i p_{Xi}] = E[\sum_i p_{Yi}]$ under any population size histories of $X$ and $Y$, so the two expected counts in the ratio are equal and $R_{X/Y}$ is expected to be $1$. A departure from $1$ at constrained sites, against $R_{X/Y} \approx 1$ at neutral sites, indicates a difference in the accumulated load.

## Expansion

The identity is $p_X(1-p_Y) - p_Y(1-p_X) = p_X - p_Y$, summed over sites; the sample proportions are unbiased for the population frequencies when sampled chromosomes are drawn at random. Under neutral Wright–Fisher drift the frequency of an allele is a martingale, so alleles segregating at the split keep the same expected frequency in both daughters, while new mutations enter each lineage at the same expected rate and also have martingale frequencies; demography changes the variance of these frequencies but not their means. Hence $E[\sum_i p_{Xi}] - E[\sum_i p_{Yi}] = 0$ and, summed over many sites, the ratio concentrates at $1$. With selection the expectation depends on dominance: for additive effects simulations of fitted African and European histories predict $R$ only slightly below $1$ for realistic distributions of selection coefficients, and recessive effects shift it in the opposite direction, so the observed $R \approx 1$ for non-synonymous sites does not show that selection was less effective after a bottleneck.

## Sources

- R. Do, D. Balick, H. Li, I. Adzhubei, S. Sunyaev and D. Reich, "No evidence that selection has been less effective at removing deleterious mutations in Europeans than in Africans", Nature Genetics 47 (2015), 126–131, main text and Online Methods ("Weighted Block Jackknife to estimate standard errors" and the definition of $R_{X/Y}$), <https://doi.org/10.1038/ng.3186> (PMC4310772).
