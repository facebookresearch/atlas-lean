# Sampled IBD segment lengths and detection error in IBD-based demographic inference

Browning and Browning (2015, Appendix) model a segment shared identical by descent by two haplotypes whose most recent common ancestor lived $g$ generations ago, with Haldane crossovers along the $2g$ meioses separating them. The conditional law given $g$ of the segment covering a fixed position (Erlang with shape $2$) and the length-bias relation (a randomly sampled segment has density proportional to $\ell^{-1}$ times the covering-segment density) are stated in [expected IBD sharing from coalescence times and Erlang segment lengths](../../structured-coalescent/ibd-sharing-under-migration/expected-ibd-sharing-from-coalescence-times-and-erlang-segment-lengths.md); applied at fixed $g$, the length bias turns the Erlang law into the exponential law with the same rate for a randomly sampled segment, in centimorgans the rate $2g/100 = g/50$. The Wright–Fisher law of the time to the most recent common ancestor under a size history, the posterior time of an observed segment with its corrections for chromosome ends, and the IBDNe moment update are stated in [the posterior TMRCA of an observed IBD segment](../../skyline-plot-estimates-of-population-size/ibd-based-estimation-of-recent-effective-size/posterior-tmrca-of-an-observed-ibd-segment.md) and [expected IBD per generation and the IBDNe moment update](../../skyline-plot-estimates-of-population-size/ibd-based-estimation-of-recent-effective-size/expected-ibd-per-generation-and-the-ibdne-update.md). Ralph and Coop (2013, Methods) model detection by a length-dependent probability of missing a true block and an exponential length-error law, and treat the recovery of the distribution of ancestry times from block counts as an ill-conditioned inverse problem whose point estimates need a regularizing penalty.

## Depends on

- [Expected IBD sharing from coalescence times and Erlang segment lengths](../../structured-coalescent/ibd-sharing-under-migration/expected-ibd-sharing-from-coalescence-times-and-erlang-segment-lengths.md)

## Expansion

1. The exponential law, with rate $g/50$ per cM, of a randomly sampled IBD segment from a common ancestor $g$ generations back, from the Erlang law of the covering segment and the length bias.
2. The detection and length-error model of Ralph and Coop.
3. Regularization of the inverse problem from block counts to ancestry times, as an estimator rather than an exact identity.

## Sources

- S. R. Browning and B. L. Browning, Accurate non-parametric estimation of recent effective population size from segments of identity by descent, Am. J. Hum. Genet. 97 (2015), 404–418, Appendix. <https://doi.org/10.1016/j.ajhg.2015.07.012>
- P. Ralph and G. Coop, The geography of recent genetic ancestry across Europe, PLoS Biol. 11 (2013), e1001555, Methods. <https://doi.org/10.1371/journal.pbio.1001555>
