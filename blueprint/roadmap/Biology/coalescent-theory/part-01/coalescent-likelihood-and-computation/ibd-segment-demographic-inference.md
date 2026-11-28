# Detection error and regularization in IBD-based demographic inference

Browning and Browning (2015, Appendix) model a segment shared identical by descent by two haplotypes whose most recent common ancestor lived $g$ generations ago, with Haldane crossovers along the $2g$ meioses separating them. The conditional law given $g$ of the segment covering a fixed position (Erlang with shape $2$) and the length-bias relation (a randomly sampled segment has density proportional to $\ell^{-1}$ times the covering-segment density) are stated in [expected IBD sharing from coalescence times and Erlang segment lengths](../../structured-coalescent/ibd-sharing-under-migration/expected-ibd-sharing-from-coalescence-times-and-erlang-segment-lengths.md), and the resulting exponential law, with rate $2g$ per Morgan ($g/50$ per cM), of the length of a randomly chosen segment is stated in [recent effective size from the IBD-shared genome fraction](../../two-locus-coalescent/recent-coalescence-from-ibd-segments/recent-effective-size-from-the-ibd-shared-genome-fraction.md); neither is restated here. The Wright–Fisher law of the time to the most recent common ancestor under a size history, the posterior time of an observed segment with its corrections for chromosome ends, and the IBDNe moment update are stated in [the posterior TMRCA of an observed IBD segment](../../skyline-plot-estimates-of-population-size/ibd-based-estimation-of-recent-effective-size/posterior-tmrca-of-an-observed-ibd-segment.md) and [expected IBD per generation and the IBDNe moment update](../../skyline-plot-estimates-of-population-size/ibd-based-estimation-of-recent-effective-size/expected-ibd-per-generation-and-the-ibdne-update.md). Ralph and Coop (2013, Methods) model detection by a length-dependent probability of missing a true block and an exponential length-error law, and treat the recovery of the distribution of ancestry times from block counts as an ill-conditioned inverse problem whose point estimates need a regularizing penalty.

## Depends on

- [Expected IBD sharing from coalescence times and Erlang segment lengths](../../structured-coalescent/ibd-sharing-under-migration/expected-ibd-sharing-from-coalescence-times-and-erlang-segment-lengths.md)
- [Recent effective size from the IBD-shared genome fraction](../../two-locus-coalescent/recent-coalescence-from-ibd-segments/recent-effective-size-from-the-ibd-shared-genome-fraction.md)

## Expansion

1. The detection and length-error model of Ralph and Coop.
2. Regularization of the inverse problem from block counts to ancestry times, as an estimator rather than an exact identity.

## Sources

- S. R. Browning and B. L. Browning, Accurate non-parametric estimation of recent effective population size from segments of identity by descent, Am. J. Hum. Genet. 97 (2015), 404–418, Appendix. <https://doi.org/10.1016/j.ajhg.2015.07.012>
- P. Ralph and G. Coop, The geography of recent genetic ancestry across Europe, PLoS Biol. 11 (2013), e1001555, Methods. <https://doi.org/10.1371/journal.pbio.1001555>
