# Geometric intergap lengths under the neutral indel model

**Model.** Align two genomes and walk along the alignment. Under the **neutral indel model**, distinct insertion–deletion events are independent and occur uniformly along the sequence, so, conditional on the survival of its left neighbour as a homologous aligned nucleotide, each site survives with the same probability $p = 1 - \rho$; $\rho$ is the indel probability per site (the indel rate).

**Proposition.** The number $L$ of homologous nucleotides between successive indels (the length of an intergap segment, IGS) is geometric:

$$\Pr(L = \ell) = \rho\,(1 - \rho)^{\ell}, \qquad \ell = 0, 1, 2, \dots,$$

irrespective of the distribution of indel lengths and of the relative frequency of insertions and deletions. Consequently the IGS-length histogram $H_\ell$ is a straight line in log-linear coordinates, $\log H_\ell = \log C + \ell \log(1 - \rho)$, and the expected distance between indels is $K = 1/\rho$ (up to an $O(1)$ convention-dependent offset).

**Excess statistic.** Fitting $C(1 - \rho)^{\ell}$ to the histogram over a length range where the neutral model holds, the fraction of nucleotides in ungapped segments that is over-represented relative to the neutral prediction is

$$\sigma = \frac{\sum_{\ell \ge \ell_{\min}} \ell\,\big(H_\ell - C(1 - \rho)^{\ell}\big)}{\sum_{\ell \ge 1} \ell\, H_\ell}.$$

Short segments ($\ell < \ell_{\min}$, with $\ell_{\min} = 20$ bp for human–mouse alignments) are excluded from the excess in the numerator only, because nearby indels are merged into single alignment gaps (gap attraction); the denominator counts all nucleotides in ungapped segments of every length $\ell \ge 1$, as in the source's formula $\sigma = \sum_{L=20}^{\infty} L(H_L - Cp^L)/\sum_{L=1}^{\infty} LH_L$.

**Properties.**

1. Indel-purifying selection, which removes indels from functional segments, lengthens some IGS and makes $\sigma > 0$.
2. Neutral variation of the indel rate (for example with G+C content or between the X chromosome and autosomes) turns the IGS distribution into a mixture of geometrics, which is convex in log-linear coordinates and also gives $\sigma > 0$; stratifying by such covariates and averaging $\sigma$ removes this contribution.
3. $\sigma$ is not itself the fraction of sites under selection; the source treats it as a rough upper bound on that fraction.

## Expansion

Conditional independence of survival given the left neighbour makes the survival of a run of $\ell$ sites $p^{\ell}$, and the run ends at the first non-surviving site, which gives the geometric law; indel length only affects what happens inside the gap, not the spacing of gaps. A mixture $\sum_k w_k \rho_k (1 - \rho_k)^{\ell}$ has $\log$-mass that is a log-sum-exp of linear functions of $\ell$, hence convex, so fitting a single line over a central range leaves excess mass in the right tail. In human–mouse alignments the IGS histogram is geometric to within 0.004% of the variance over 20–50 bp, ancestral repeats (expected to evolve neutrally) give $\sigma \approx 0.007$, and the whole genome gives $\sigma \approx 0.11$.

## Sources

- Lunter G, Ponting CP, Hein J, "Genome-wide identification of human functional DNA using a neutral indel model" (2006), Results, "The Neutral Indel Model" and "Accounting for Indel Rate Variation", and Materials and Methods, "Intergap length histograms", <https://doi.org/10.1371/journal.pcbi.0020005>, PMCID PMC1326222.
