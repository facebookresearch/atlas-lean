# Variant-edge genotypes determine walks

Let $B$ be a bidirected pangenome graph with reference tree $T$, as in [Bidirected pangenome graphs and variant edges](bidirected-pangenome-graphs-and-variant-edges.md).

**Theorem.** Given the starting and ending binodes of a walk $W$, its genotype $x(W) = (x_e(W))$ over the variant edges determines $W$ up to the order in which it traverses cycles: it determines how many times $W$ visits every binode and traverses every biedge, and any two walks with the same endpoints and genotype differ only in the relative order of subwalks that begin and end at the same binode. The statement holds for every choice of reference tree.

**Reconstruction.** From $x(W)$ and the endpoints:

1. For each traversal of a variant edge $(u, v)$, add $u$ to the sinks if $u \in V^+$ and $u^c$ to the sources otherwise; add $v$ to the sources if $v \in V^+$ and $v^c$ to the sinks otherwise.
2. Add the endpoints according to the parity of inversion traversals: with an even number, the start node is a source and the end node a sink; with one more $+\!\to\!-$ than $-\!\to\!+$ switch, both endpoints are sinks; with one more $-\!\to\!+$ switch, both are sources. A valid genotype now has equally many sources and sinks.
3. From each sink, climb $T^+$ against edge direction until reaching a source with remaining multiplicity, recording the tree edges used and decrementing that source. Each node has at most one parent, so no search is needed.
4. If a climb reaches the root without meeting an available source, the genotype corresponds to no single walk.

## Depends on

- [Bidirected pangenome graphs and variant edges](bidirected-pangenome-graphs-and-variant-edges.md)

## Proof sketch

The visit-count formula $|D(v)\cap\mathrm{sinks}(W)| - |(D(v) \setminus \{v\})\cap\mathrm{sources}(W)|$ depends only on the multisets of sources and sinks, not on their order, and these multisets are read off the genotype and the endpoints. So the genotype fixes the number of visits to every binode, hence the number of traversals of every tree edge; the variant-edge traversals are the genotype itself. A walk is determined by its edge multiset up to the ordering of closed subwalks, which proves the theorem (Theorem 1 and Algorithm 3 of the source). Consequently the variant edges act as a basis for differences between haplotypes: the symmetric difference of two walks' edge sets is captured by their genotype difference.

## Sources

- P. Salehi Nowbandegani, S. Zhang, H. Hu, H. Li, L. J. O'Connor, "Defining and cataloging variants in pangenome graphs", Cell Genomics (2026), <https://doi.org/10.1016/j.xgen.2026.101327> (PMC13576716).
