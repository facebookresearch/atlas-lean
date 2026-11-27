# Hi-C scaffolding by weighted matching

Ordering and orienting assembled contigs into chromosome-scale scaffolds from Hi-C contact counts,
by scoring a graph on contig ends with locally normalized ("best buddy") weights and laying out
contigs through iterated greedy weighted matchings.

- [Best-buddy edge weights for Hi-C scaffold graphs](best-buddy-edge-weights-for-hi-c-scaffold-graphs.md)
- [Greedy matching layout of contigs](greedy-matching-layout-of-contigs.md)

## Sources

- J. Ghurye, A. Rhie, B. P. Walenz et al., "Integrating Hi-C links with assembly graphs for chromosome-scale assembly", *PLoS Computational Biology* 15 (2019) e1007273, <https://doi.org/10.1371/journal.pcbi.1007273> (PMC6719893), Methods, "Scaffold graph construction" and "Contig layout".
