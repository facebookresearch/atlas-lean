# Density of recent coalescence statistic

**Definition.** Fix a time horizon $T$ (in generations) and a set $\mathcal P$ of analysed pairs of haploid genomes. For a pair $(a, b)$ and a genomic site $x$, let $q_{ab}(x) = P(t_{ab}(x) \le T \mid \text{data})$ be the posterior probability, from a coalescent hidden Markov model of the pair's TMRCA along the genome, that the pair coalesced within the last $T$ generations at $x$. The density of recent coalescence at $x$ is

$$\mathrm{DRC}_T(x) = \frac{1}{|\mathcal P|}\sum_{(a,b)\in\mathcal P} q_{ab}(x) = \int_0^T \bar p_x(t)\, dt, \qquad \bar p_x(t) = \frac{1}{|\mathcal P|}\sum_{(a,b)\in\mathcal P} p_{ab,x}(t),$$

where $p_{ab,x}$ is the pair's posterior TMRCA density at $x$; the two forms agree because integration up to $T$ commutes with the average over pairs. It estimates the probability that a random pair coalesced at $x$ within the last $T$ generations, and it is averaged over the sites of a short genomic window (0.05 cM in both sources).

**Two ways of obtaining the inputs.**

- From full posterior decodings: the [ASMC hidden Markov model](asmc-hidden-markov-model-for-pairwise-coalescence-times.md) gives $p_{ab,x}$ for every analysed pair, and the statistic is the integral of their average (Palamara et al.).
- From detected IBD segments: an IBD detection method reports, for each detected segment of a pair, a quality score equal to the posterior probability of coalescence within $T$ generations, and $q_{ab}(x)$ is the score of the segment covering $x$, or $0$ if no segment of that pair covers $x$ (Nait Saada et al., who call the resulting average an estimate of the same density of recent coalescence). Pairs without a reported segment contribute zero, so the sum runs in effect over detected segments only, which makes the computation feasible for hundreds of thousands of genomes.

**Null law and test.** For $n$ sampled haplotypes from a neutrally evolving population of recent effective size $N$ with $n \ll N$ and $T$ small, $\mathrm{DRC}_T$ is approximately Gamma distributed. Fitting a Gamma law to $\mathrm{DRC}_T$ in putatively neutral windows gives approximate one-sided $p$-values, with a Bonferroni threshold across windows; an excess of recent coalescence in a window is evidence of recent positive selection, which shortens genealogies around the selected allele.

## Depends on

- [ASMC hidden Markov model for pairwise coalescence times](asmc-hidden-markov-model-for-pairwise-coalescence-times.md)

## Expansion

When $n \ll N$, few coalescences happen within $T$ generations; each pair's coalescence time is then nearly exponential and nearly independent of the others, so the count of early coalescence events, and its normalized version $\mathrm{DRC}_T$, is close to Gamma distributed. At a neutral site, each pair's indicator of coalescence before $T$ has expectation $P(t \le T) \approx T/N$, so $\mathrm{DRC}_T$ is the site-wise analogue of the genome-wide shared fraction used to estimate a [recent effective size from IBD sharing](../recent-coalescence-from-ibd-segments/recent-effective-size-from-the-ibd-shared-genome-fraction.md). A beneficial allele that rises rapidly forces its carriers to share a recent common ancestor, which piles posterior mass at small $t$ for many pairs near the selected site. The significance computation treats pairs as coalescing independently, which is anticonservative, while fitting the null to real data (which may contain weakly selected regions) and Bonferroni correction across correlated windows are conservative; known selected regions must be excluded, iteratively, from the neutral set.

With $T = 150$ generations, the statistic is sensitive to selection within roughly the last 20,000 years. Applied with ASMC decodings to 113,732 British-ancestry UK Biobank samples (about 2.2 billion haploid pairs, 63,103 windows, threshold $0.05/63{,}103$) it found 12 genome-wide significant loci, six of them known targets such as LCT, HLA and MC1R. Applied with $T = 50$ to IBD segments in about 487,000 British genomes over 52,003 windows, the scan reported genome-wide significant loci such as one near MRC1.

## Sources

- P. F. Palamara, J. Terhorst, Y. S. Song and A. L. Price, "High-throughput inference of pairwise coalescence times identifies signals of selection and enriched disease heritability", *Nature Genetics* 50 (2018), 1311–1317, Online Methods sections "Detection of recent positive selection" and "Null model calibration", <https://doi.org/10.1038/s41588-018-0177-x> (PMC6145075).
- J. Nait Saada, G. Kalantzis, D. Shyr, F. Cooper, M. Robinson, A. Gusev, P. F. Palamara, "Identity-by-descent detection across 487,409 British samples reveals fine scale population structure and ultra-rare variant associations", Nature Communications (2020), Methods ("FastSMC validation step" and "Detection of recent positive selection"), <https://doi.org/10.1038/s41467-020-19588-x>.
