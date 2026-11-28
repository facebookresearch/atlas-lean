# Fraction of recessive disease due to founder events

Consider the two alleles carried by one individual at a locus in an endogamous group. Assume:

- with probability $F$ (Wright's fixation index from consanguinity) the two alleles coalesce within the last few generations because the parents are related;
- otherwise, with probability $D$, they coalesce more recently than a reference event (in the source, the mixture of the ancestral populations of the group) because of a founder event specific to the group;
- cases of a rare recessive disease arise from homozygosity for alleles identical by descent through one of these two routes.

Then the fraction of recessive disease cases attributable to founder events rather than consanguinity is

$$\frac{D(1 - F)}{F + D(1 - F)} .$$

## Expansion

The two routes to recent identity are disjoint: consanguinity contributes probability $F$, and founder-event identity requires first escaping consanguinity (probability $1 - F$) and then coalescing in the founder bottleneck (probability $D$). Conditioning on recent identity by descent gives the ratio. The estimate of $D$ comes from the group-specific drift fitted in an admixture model whose $f$-statistics are corrected for inbreeding. The source finds that many Indian groups have strong founder events, so that a substantial share of recessive disease would persist even without consanguinity, which motivates group-specific mapping of recessive diseases.

## Sources

- D. Reich, K. Thangaraj, N. Patterson, A. L. Price and L. Singh, "Reconstructing Indian population history", *Nature* 461 (2009), 489–494, footnote to Table 2 (fraction of recessive diseases due to founder events), <https://doi.org/10.1038/nature08365> (PMC2842210).
