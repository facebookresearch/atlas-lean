# Interleaved breakpoint clusters

Let a set of intrachromosomal structural variants on one chromosome be given, each variant $v$ determined by the interval $I_v = [a_v, b_v]$ between its two breakpoints, $a_v < b_v$. Two variants $u, v$ are **nested** if one interval contains the other, $I_u \subseteq I_v$ or $I_v \subseteq I_u$, and **interleaved** if the intervals overlap without containment,

$$a_u < a_v < b_u < b_v \quad\text{or}\quad a_v < a_u < b_v < b_u .$$

The **interleaving graph** of the chromosome has the intrachromosomal variants as vertices and an edge between every interleaved pair. An **interleaved cluster** is a connected component of this graph, and the cluster examined on each chromosome is the component with the most variants; the minimum cluster size for a call is left to the calling criteria.

The distinction separates generating mechanisms only in part. Breakage–fusion–bridge cycles produce nested fold-back inversions, and sequential rearrangement processes tend to produce nested or disjoint pairs; but overlapping tandem duplications can also produce interleaved pairs (a duplication of $[10, 20]$ followed by one of $[15, 25]$ gives $10 < 15 < 20 < 25$), as can template-switching replication errors. A single shattering of a chromosome into fragments that are rejoined in a random order produces, with high probability, many interleaved pairs: if $2k$ breakpoints are placed on the chromosome and the fragments are joined by a uniformly random matching, the probability that a given pair of joins is nested rather than interleaved is bounded away from one, so a cluster of $k$ joins contains order $k^2$ interleaved pairs in expectation. Interleaving is therefore the signature used to call a one-off shattering event, and it detects such events in copy-number profiles that do not oscillate cleanly between two levels, including profiles disturbed by later amplifications or by aneuploidy.

## Expansion

That random joining yields interleaving is the standard chord-crossing count: draw the $2k$ breakpoints on a line and join them in pairs at random; two chords either nest, interleave, or lie apart, and the uniform matching puts constant probability on the interleaved configuration for a pair chosen at random. The criterion is one-sided: interleaving is not proof of a single catastrophic event, since overlapping tandem duplications and template-switching replication errors can also generate interleaved joins; this is why the detection rule combines interleaving with the independent criteria on copy-number oscillation, on the mix of join orientations, and on the spatial distribution of breakpoints.

## Sources

- I. Cortés-Ciriano, J. J.-K. Lee, R. Xi et al., "Comprehensive analysis of chromothripsis in 2,658 human cancers using whole-genome sequencing", Nature Genetics 52 (2020), 331–341, main text ("Detection of chromothripsis", Fig. 1) and Methods ("Characterization of chromothripsis events using ShatterSeek"), <https://doi.org/10.1038/s41588-019-0576-7>, PMCID PMC7058534.
- ShatterSeek tutorial (the package documentation linked from the paper's Methods), section 2.1 ("Detection of clusters of interleaved SVs"), <https://github.com/parklab/ShatterSeek/blob/master/inst/tutorial/tutorial.pdf>.
