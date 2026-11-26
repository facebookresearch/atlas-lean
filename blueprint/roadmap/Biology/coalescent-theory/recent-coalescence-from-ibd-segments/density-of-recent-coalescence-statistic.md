# Density of recent coalescence statistic

**Definition.** Fix a time threshold $T$ (in generations) and a sample of haplotype pairs $\mathcal P$. For a pair $(a,b)$ and a genomic site $x$, let $q_{ab}(x) = P(t_{ab}(x) \le T \mid \text{data})$ be the posterior probability, from a coalescent hidden Markov model of the pair's TMRCA along the genome, that the pair coalesced within the last $T$ generations at $x$ (the IBD quality score of a detected segment covering $x$; $0$ if no segment covers $x$). The density of recent coalescence is

$$\mathrm{DRC}_T(x) = \frac{1}{|\mathcal P|}\sum_{(a,b)\in\mathcal P} q_{ab}(x),$$

an estimate of the probability that a random pair coalesced at $x$ within the last $T$ generations, usually averaged over short windows (for example $0.05$ cM).

**Null law and test.** For $n$ samples from a population of recent effective size $N \gg n$ evolving neutrally, $\mathrm{DRC}_T$ is approximately Gamma distributed. Fitting a Gamma law to windows in putatively neutral regions gives approximate one-sided p-values; an excess of recent coalescence in a window is evidence of recent positive selection, which shortens genealogies around the selected allele.

## Depends on

- [Recent effective size from the IBD-shared genome fraction](recent-effective-size-from-the-ibd-shared-genome-fraction.md)

## Expansion

At a neutral site, each pair's indicator of coalescence before $T$ has expectation $P(t \le T) \approx T/N$, so $\mathrm{DRC}_T$ is the site-wise analogue of the genome-wide shared fraction used to estimate $N$; a sweep in the last $T$ generations raises it locally. The significance computation treats pairs as coalescing independently, which is anticonservative, while fitting the null to real data (which may contain weakly selected regions) and Bonferroni correction across correlated windows are conservative; known selected regions must be excluded, iteratively, from the neutral set. Applied with $T = 50$ to about 487,000 British genomes over 52,003 windows, the scan reported genome-wide significant loci such as one near MRC1.

## Sources

- J. Nait Saada, G. Kalantzis, D. Shyr, F. Cooper, M. Robinson, A. Gusev, P. F. Palamara, "Identity-by-descent detection across 487,409 British samples reveals fine scale population structure and ultra-rare variant associations", Nature Communications (2020), Methods ("FastSMC validation step" and "Detection of recent positive selection"), <https://doi.org/10.1038/s41467-020-19588-x>.
