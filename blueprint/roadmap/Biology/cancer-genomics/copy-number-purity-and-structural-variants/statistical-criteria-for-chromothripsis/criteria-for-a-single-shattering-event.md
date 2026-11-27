# Criteria for calling a single shattering event from copy number and rearrangements

Fix a chromosome in one tumour genome, with its segmented copy-number profile and its set of structural variants (SVs), and let the **cluster** be the [interleaved cluster](interleaved-breakpoint-clusters.md) of the chromosome's intrachromosomal SVs that is examined, with its region spanning the cluster's outermost breakpoints. The calling rule combines the following statistics of the cluster.

1. **Cluster size.** $n_{\text{intra}}$, the number of intrachromosomal SVs in the cluster, and $n_{\text{inter}}$, the number of interchromosomal SVs with a breakpoint in the cluster region.

2. **Copy-number oscillation.** $N_{\text{osc}}$, the largest number of contiguous copy-number segments in the cluster region whose copy number oscillates between two states. In a near-diploid genome an event is **canonical** when more than $60\%$ of the segments of the affected region oscillate between two states.

3. **Fragment joins test.** Let the four orientation classes of a join be duplication-like, deletion-like, head-to-head inversion and tail-to-tail inversion, with observed counts $(n_1, n_2, n_3, n_4)$ among the cluster's intrachromosomal SVs, summing to $n$. Random rejoining of fragments makes the four classes roughly equally likely; the test of $p_1 = p_2 = p_3 = p_4 = 1/4$ uses the goodness-of-fit statistic
$$X^2 = \sum_{i=1}^{4} \frac{(n_i - n/4)^2}{n/4} \sim \chi^2_3 \quad \text{under the null of equal proportions,}$$
and the criterion holds when equal proportions are not rejected.

4. **Chromosomal breakpoint enrichment test.** A binomial test, corrected for mappability, of whether the chromosome's SV breakpoint rate exceeds the genome-wide rate; the criterion holds when the enrichment is significant.

5. **Random distribution of breakpoints test.** A test of whether the distribution of the cluster's breakpoints differs from an exponential distribution, the law of distances between consecutive breakpoints scattered at random (Korbel and Campbell's clustering criterion); the criterion holds when the difference is significant.

**Calling rule.** The chromosome carries a chromothripsis region

- with **high confidence** if either $n_{\text{intra}} \ge 6$, $N_{\text{osc}} \ge 7$, the fragment joins test holds, and the enrichment test (4) or the random-distribution test (5) holds; or $n_{\text{intra}} \ge 3$, $n_{\text{inter}} \ge 4$, $N_{\text{osc}} \ge 7$ and the fragment joins test holds;
- with **low confidence** if $n_{\text{intra}} \ge 6$, $4 \le N_{\text{osc}} \le 6$, the fragment joins test holds, and test (4) or test (5) holds.

The fragment joins test is what makes a cluster of rearrangements evidence for random rejoining: a process acting in successive rounds concentrates one or two orientation classes (tandem duplications, or deletions), while fragments reassembled in one step in a random order equidistribute them. Tests (4) and (5) require the breakpoints to be concentrated, on the chromosome or within the cluster, beyond what scattered background rearrangement produces.

## Depends on

- [Interleaved breakpoint clusters](interleaved-breakpoint-clusters.md)

## Expansion

The criteria are nearly independent summaries of the same breakpoint set, which is why a conjunction is used rather than a single composite score: oscillation detects loss of fragments between rejoined pieces, interleaving detects the order of joins, the orientation test detects the symmetry of joining, and the enrichment and random-distribution tests detect whether the shattering was confined. The enrichment test can mislead for focal events in highly rearranged genomes, where other chromosomes carry comparable numbers of SVs, which is why either of the two concentration tests suffices. The thresholds on $n_{\text{intra}}$ and $N_{\text{osc}}$ are calibrated by manual curation, not derived, and are the main lever on the frequency reported in a cohort; the minimum of six SVs on the main routes misses focal clusters of fewer rearrangements, which overlap with tandem-duplication and breakage–fusion–bridge patterns, and the published rule accepts the loss of such small events in exchange for specificity. Applying these criteria to whole-genome sequencing of 2,543 tumour–normal pairs across 37 cancer types gave high-confidence calls in more than half the samples in several types, far above the few percent estimated from array-based copy-number data alone, the difference coming from events that do not oscillate cleanly between exactly two levels and from events spanning several chromosomes, which only the rearrangement-based criteria can link.

## Sources

- I. Cortés-Ciriano, J. J.-K. Lee, R. Xi et al., "Comprehensive analysis of chromothripsis in 2,658 human cancers using whole-genome sequencing", Nature Genetics 52 (2020), 331–341, main text (Fig. 1a,b; minimum of six SVs; high-confidence $N_{\text{osc}} \ge 7$ and low-confidence $4$–$6$ oscillating segments), Methods ("Characterization of chromothripsis events using ShatterSeek") and Supplementary Note (criteria and thresholds), <https://doi.org/10.1038/s41588-019-0576-7>, PMCID PMC7058534.
- ShatterSeek tutorial (the package documentation linked from the paper's Methods), sections 2.2 ("Statistical criteria implemented in ShatterSeek") and 3 ("Recommended cut-off values to interpret the output of ShatterSeek"), <https://github.com/parklab/ShatterSeek/blob/master/inst/tutorial/tutorial.pdf>.
