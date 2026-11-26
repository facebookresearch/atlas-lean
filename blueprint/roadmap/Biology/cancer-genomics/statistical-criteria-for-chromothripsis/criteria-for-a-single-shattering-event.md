# Criteria for calling a single shattering event from copy number and rearrangements

Fix a chromosome in one tumour genome, with its segmented copy-number profile and its set of structural variants. A single shattering-and-rejoining event is called when all of the following hold.

1. **Copy-number oscillation.** The affected region contains a run of adjacent segments whose copy number alternates between two states (or, in an aneuploid genome, three). Let $N_{\text{osc}}$ be the length of the longest such run; the call is high confidence for $N_{\text{osc}} \ge 7$ and low confidence for $4 \le N_{\text{osc}} \le 6$. In a near-diploid genome an event is **canonical** when more than $60\%$ of the segments of the affected region oscillate between two states.

2. **Interleaving.** The breakpoints form an [interleaved cluster](interleaved-breakpoint-clusters.md) rather than a nested one.

3. **Equidistribution of join types.** Let the four orientation classes of a join be duplication-like, deletion-like, head-to-head inversion and tail-to-tail inversion, with observed counts $(n_1, n_2, n_3, n_4)$ summing to $n$. Random rejoining of fragments makes the four classes roughly equally likely, so the call requires consistency with $p_1 = p_2 = p_3 = p_4 = 1/4$, tested by the goodness-of-fit statistic
$$X^2 = \sum_{i=1}^{4} \frac{(n_i - n/4)^2}{n/4} \sim \chi^2_3 \quad \text{under the null of equal proportions.}$$

4. **Spatial randomness of breakpoints.** Conditional on the affected region, the breakpoint positions are consistent with a uniform distribution over that region, tested by the usual one-sample goodness-of-fit statistic for uniformity on an interval.

Criteria 3 and 4 are the ones that make a clustered set of rearrangements evidence for simultaneity: a process acting in successive rounds concentrates one or two orientation classes (tandem duplications, or deletions) and clusters breakpoints near earlier ones, while fragments reassembled in one step in a random order equidistribute orientations and positions.

## Depends on

- [Interleaved breakpoint clusters](interleaved-breakpoint-clusters.md)

## Expansion

The four tests are nearly independent summaries of the same breakpoint set, which is why a conjunction is used rather than a single composite score: oscillation detects loss of fragments between rejoined pieces, interleaving detects the order of joins, the orientation test detects the symmetry of joining, and the uniformity test detects whether the shattering was confined. The thresholds on $N_{\text{osc}}$ are calibrated, not derived, and are the main lever on the frequency reported in a cohort; a lower threshold admits focal clusters of few rearrangements, which overlap with tandem-duplication and breakage–fusion–bridge patterns, and the published rule accepts the loss of such small events in exchange for specificity. Applying these criteria to whole-genome sequencing of 2,543 tumour–normal pairs across 37 cancer types gave high-confidence calls in more than half the samples in several types, far above the few percent estimated from array-based copy-number data alone, the difference coming from events that do not oscillate cleanly between exactly two levels and from events spanning several chromosomes, which only the rearrangement-based criteria can link.

## Sources

- I. Cortés-Ciriano, J. J.-K. Lee, R. Xi et al., "Comprehensive analysis of chromothripsis in 2,658 human cancers using whole-genome sequencing", Nature Genetics 52 (2020), 331–341, main text (Fig. 1a,b, criteria and confidence thresholds) and Methods ("Detection of chromothripsis-like patterns"), <https://doi.org/10.1038/s41588-019-0576-7>, PMCID PMC7058534.
