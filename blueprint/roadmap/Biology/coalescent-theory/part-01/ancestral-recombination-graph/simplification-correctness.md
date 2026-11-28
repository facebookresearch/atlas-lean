# Tree-sequence simplification

Given a tree sequence and a chosen subset of its nodes as samples, simplification (Kelleher, Thornton, Ashander and Ralph 2018, section "Tree sequence simplification") produces the smallest tree sequence that still describes the history of those samples, characterized by four properties: every marginal tree equals the subtree of the corresponding input tree induced by the samples; every non-sample vertex of a marginal tree has at least two children, so unary non-sample vertices are suppressed, while a sample vertex is kept even when it is unary (in the boundary case of two samples, one the only child of the other, the output tree is that two-vertex chain); nodes and edges ancestral to none of the samples are removed; and no two adjacent edges $(\ell, x, p, c)$ and $(x, r, p, c)$ remain that could be merged into $(\ell, r, p, c)$. The algorithm works backward in time from the samples, propagating the segments of ancestral material each node carries and recording an edge whenever segments of different samples meet, in the manner of Hudson's coalescent simulation algorithm with events fixed by the recorded history; its running time is linear in the number of input edges in the reported benchmarks. Simplification does not keep every event of an ancestral recombination graph: Wong et al. (2024, section on sample-resolved graphs and Fig. 3) show that it removes a grand most recent common ancestor reached after every segment has coalesced and an edge created by a recombination that falls in non-ancestral material.

## Expansion

1. The subtree of a marginal tree induced by a set of samples, with unary non-sample vertices suppressed; unary sample vertices are kept, as in the two-sample chain where one sample is the only child of the other.
2. The four defining properties of the simplified output, and its uniqueness up to renumbering of nodes.
3. The backward sweep over edges in time order, maintaining for each node the ancestral segments mapped to output nodes, and its correctness: the induced marginal trees and the sample genotypes are preserved at every position.
4. Events of the full graph that the output does not represent, with the examples of Wong et al. (2024, Fig. 3).

## Sources

- J. Kelleher, K. R. Thornton, J. Ashander and P. L. Ralph, Efficient pedigree recording for fast population genetics simulation, PLoS Comput. Biol. 14 (2018), e1006581, section "Tree sequence simplification" and Fig. 7. <https://doi.org/10.1371/journal.pcbi.1006581>
- Y. Wong et al., A general and efficient representation of ancestral recombination graphs, Genetics 228 (2024), iyae100, Fig. 3 and the surrounding text. <https://doi.org/10.1093/genetics/iyae100>
