# Frequency-binned standardized integrated haplotype score

Let a biallelic core site have derived allele frequency $p \in (0,1)$ in a sample of haplotypes, and let
$\mathrm{iHH}_A$ and $\mathrm{iHH}_D$ denote the [integrated extended haplotype homozygosity to a
homozygosity cutoff](integrated-ehh-to-a-homozygosity-cutoff.md) computed with respect to the ancestral and
the derived core allele, both defined and positive at that site. Write

$$X = \log\frac{\mathrm{iHH}_A}{\mathrm{iHH}_D}$$

for the unstandardized integrated haplotype score at that site. Let the frequency bin of the site be the
collection of all scored sites whose derived allele frequency equals $p$, and let $E_p[X]$ and
$\mathrm{SD}_p[X]$ be the empirical mean and standard deviation of $X$ over that bin (the variance taken with
the normalization used for the standardization). If $\mathrm{SD}_p[X] > 0$, the standardized integrated
haplotype score is

$$\mathrm{iHS} = \frac{X - E_p[X]}{\mathrm{SD}_p[X]};$$

if $\mathrm{SD}_p[X] = 0$, for instance when all sites of the bin have the same value of $X$ (a bin with a
single site included), $\mathrm{iHS}$ is undefined for the sites of that bin.

In every bin with $\mathrm{SD}_p[X] > 0$, the values of $\mathrm{iHS}$ over the bin have empirical mean $0$
and empirical variance $1$ (with the same normalization), hence its values are comparable across core sites
of different allele frequencies. It is an empirical standardization against a reference collection of sites,
not a test statistic with a known null distribution, so it supplies no formal significance level on its own.
Large negative values indicate unusually long haplotypes carrying the derived allele and large positive
values unusually long haplotypes carrying the ancestral allele.

## Depends on

- [Integrated EHH of an empirical haplotype sample to a homozygosity cutoff](integrated-ehh-to-a-homozygosity-cutoff.md)

## Proof depends on

Its only claim beyond the definition is the elementary computation that centring and scaling a finite
collection with positive standard deviation gives mean $0$ and variance $1$.

## Expansion

Under neutrality a low-frequency allele is on average younger than a high-frequency one and therefore sits
on a longer conserved haplotype, so $E_p[X]$ and $\mathrm{SD}_p[X]$ both vary systematically with $p$.
Centering and scaling within a frequency bin removes that confounding, leaving a quantity whose magnitude
measures how unusual the haplotype structure at a site is relative to other sites of the same allele
frequency. Equation (2) of the source states this definition, with the expectation and standard deviation
estimated from the empirical distribution of $X$ at sites matching the frequency of the core site. The
[star-genealogy integrated haplotype score](ihs.md) is the model counterpart of $X$, built from the
[one-sided integrated haplotype homozygosity](ihh.md).

## Sources

- B. F. Voight, S. Kudaravalli, X. Wen and J. K. Pritchard, "A map of recent positive selection in the human genome", PLoS Biology 4 (2006), e72, <https://doi.org/10.1371/journal.pbio.0040072> (PMC1382018). (Equation 2.)
