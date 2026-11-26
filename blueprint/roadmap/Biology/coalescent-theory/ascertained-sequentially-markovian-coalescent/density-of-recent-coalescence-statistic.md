# Density of recent coalescence statistic

Given posterior pairwise TMRCA distributions from the [ASMC hidden Markov model](asmc-hidden-markov-model-for-pairwise-coalescence-times.md) for all analysed pairs of haploid genomes at a site, average them over pairs and renormalize to obtain the average pairwise coalescence distribution $\bar p(t)$ at that site. For a time horizon $T$ (in generations), the density of recent coalescence is

$$\mathrm{DRC}_T = \int_0^T \bar p(t)\, dt,$$

averaged over the sites of a genomic window (0.05 cM in the source). For $n$ sampled haplotypes from a population of recent effective size $N$ with $n \ll N$ and $T$ small, $\mathrm{DRC}_T$ is approximately Gamma distributed under neutrality, so approximate $p$-values are obtained by fitting a Gamma law to $\mathrm{DRC}_T$ in putatively neutral windows and applying a Bonferroni threshold across windows. Large values indicate recent positive selection.

## Expansion

When $n \ll N$, few coalescences happen within $T$ generations; each pair's coalescence time is then nearly exponential and nearly independent of the others, so the count of early coalescence events, and its normalized version $\mathrm{DRC}_T$, is close to Gamma distributed. A beneficial allele that rises rapidly forces its carriers to share a recent common ancestor, which piles posterior mass at small $t$ for many pairs near the selected site. With $T = 150$ generations, the statistic is sensitive to selection within roughly the last 20,000 years. Applied to 113,732 British-ancestry UK Biobank samples (about 2.2 billion haploid pairs, 63,103 windows, threshold $0.05/63{,}103$) it found 12 genome-wide significant loci, six of them known targets such as LCT, HLA and MC1R.

## Sources

- P. F. Palamara, J. Terhorst, Y. S. Song and A. L. Price, "High-throughput inference of pairwise coalescence times identifies signals of selection and enriched disease heritability", *Nature Genetics* 50 (2018), 1311–1317, Online Methods sections "Detection of recent positive selection" and "Null model calibration", <https://doi.org/10.1038/s41588-018-0177-x> (PMC6145075).
