# Frequency-binned standardized integrated haplotype score

Let a biallelic core site have derived allele frequency $p \in (0,1)$ in a sample of haplotypes, and let
$\mathrm{iHH}_A$ and $\mathrm{iHH}_D$ denote the integrated extended haplotype homozygosity computed with
respect to the ancestral and the derived core allele. Write
$$X = \log\frac{\mathrm{iHH}_A}{\mathrm{iHH}_D}$$
for the unstandardized integrated haplotype score at that site. The standardized integrated haplotype
score is
$$\mathrm{iHS} = \frac{X - E_p[X]}{\mathrm{SD}_p[X]},$$
where $E_p[X]$ and $\mathrm{SD}_p[X]$ are the mean and the standard deviation of $X$ over the collection of
all scored sites whose derived allele frequency equals $p$, so that the standardization is carried out
separately within each derived-frequency bin.

By construction $\mathrm{iHS}$ has mean $0$ and variance $1$ within every frequency bin, hence its values are
comparable across core sites of different allele frequencies. It is an empirical standardization against a
reference collection of sites, not a test statistic with a known null distribution, so it supplies no
formal significance level on its own. Large negative values indicate unusually long haplotypes carrying
the derived allele and large positive values unusually long haplotypes carrying the ancestral allele.

## Depends on

- [Unstandardized star-genealogy integrated haplotype score](ihs.md)
- [One-sided integrated haplotype homozygosity](ihh.md)

## Expansion

Under neutrality a low-frequency allele is on average younger than a high-frequency one and therefore sits
on a longer conserved haplotype, so $E_p[X]$ and $\mathrm{SD}_p[X]$ both vary systematically with $p$.
Centering and scaling within a frequency bin removes that confounding, leaving a quantity whose magnitude
measures how unusual the haplotype structure at a site is relative to other sites of the same allele
frequency. Equation (2) of the source states this definition, with the expectation and standard deviation
estimated from the empirical distribution of $X$ at sites matching the frequency of the core site.

## Sources

- B. F. Voight, S. Kudaravalli, X. Wen and J. K. Pritchard, "A map of recent positive selection in the human genome", PLoS Biology 4 (2006), e72, <https://doi.org/10.1371/journal.pbio.0040072> (PMC1382018). (Equation 2.)
