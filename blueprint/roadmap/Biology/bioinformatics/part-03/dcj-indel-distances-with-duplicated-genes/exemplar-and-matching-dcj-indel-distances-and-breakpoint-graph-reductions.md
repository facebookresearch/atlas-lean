# Exemplar and matching DCJ-indel distances and their breakpoint-graph reductions

**Setting.** Genomes $\Gamma$ and $\Pi$ are sets of linear or circular chromosomes written as strings of signed genes. The *breakpoint graph* (BPG) has two vertices per gene, its head $a_h$ and tail $a_t$, and two edge types: the adjacencies of $\Gamma$ and the adjacencies of $\Pi$. Telomeres of linear chromosomes attach to a special CAP vertex. A double-cut-and-join (DCJ) operation cuts two adjacencies of one genome and rejoins the four ends the other way. Without duplications, the DCJ distance with insertions and deletions (indels) has a closed form in terms of the numbers of cycles and of the classes of paths of the BPG, sorted by the type of their open end vertices and their parity. With duplicated gene families the distance is NP-hard. There are two standard ways to resolve duplicates.

- **DCJ-Indel-Exemplar distance:** for each gene family keep exactly one occurrence in each genome and delete the rest. The distance is the minimum DCJ-indel distance over all such *exemplar* string pairs.
- **DCJ-Indel-Matching distance:** match the occurrences of each family one-to-one across the genomes and relabel the matched copies as distinct genes. The distance is the minimum DCJ-indel distance over all such *matchings*.

A BPG vertex is *regular* if it meets exactly one edge of each type, and *irregular* otherwise. Duplicated genes create irregular vertices, and resolving the duplicates amounts to choosing which edges to keep at each irregular vertex.

**Theorem.**

1. *(Fixing 2-cycles.)* In the BPG, an irregular subgraph that is a cycle of length $2$ can be fixed before the search, that is, kept in the solution, without changing the optimal exemplar or matching distance.
2. *(Component decomposition.)* The DCJ-Indel-Exemplar (respectively Matching) distance is optimal iff the choices of exemplar edges (respectively the cycle decomposition) are optimal within each connected component of the BPG. So the global problem splits into independent subproblems on connected components.
3. *(Regular parts.)* As long as no irregular vertices are involved, regular subgraphs can be used to decompose the multiple breakpoint graph of the median problem. Vertices of singleton genes are stable under every exemplar or matching choice, so they can be bridged out, leaving a smaller graph on the dynamic vertices only.

These reductions keep exact branch-and-bound searches for both distances small on realistic genomes. Upper bounds come from any feasible exemplar or matching. Lower bounds come from deleting all unresolved families for the exemplar variant, or from breakpoint counts for the matching variant.

## Expansion

Item 1 extends the corresponding result of Shao et al. for the matching DCJ distance without indels. In components consisting only of cycles the argument is identical. In components with paths it still applies, because no path contributes more to the distance formula than a cycle does. For item 2, the DCJ-indel distance is $N$ minus a sum of contributions of the individual cycles and paths, plus a correction from the path counts. Edge choices in different components affect disjoint sets of these objects. If some component's choice could be improved, swapping in the better choice would improve the total, so optimizing each component separately optimizes the total. Regular components admit only one choice. Both resolutions of duplicates, deletion (exemplar) and relabeling (matching), become searches over local edge choices at irregular vertices. This is also the basis of a Lin–Kernighan-style local search for the DCJ-indel median of three genomes.

These are the two theorems and the lemma of the optimization-methods section of the source.

## Sources

- Z. Yin, J. Tang, S. W. Schaeffer, D. A. Bader, "Exemplar or Matching: Modeling DCJ Problems with Unequal Content Genome Data", arXiv:1705.06559 (2017). <https://doi.org/10.48550/arXiv.1705.06559>
