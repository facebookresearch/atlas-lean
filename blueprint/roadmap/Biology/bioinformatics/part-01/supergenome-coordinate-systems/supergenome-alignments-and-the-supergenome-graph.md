# Supergenome alignments and the supergenome graph

Let $\mathcal G$ be a finite set of genome assemblies, each a set of contigs, and let $\mathcal A$ be a multiple sequence alignment whose blocks $B$ are sets of aligned sequence intervals; write $\pi_G(B)$ for the intervals of assembly $G$ in $B$. The alignment is

- complete if every position of every assembly lies in some block;
- irredundant if $\pi_G(B') \cap \pi_G(B'') = \emptyset$ for distinct blocks;
- injective if no block contains more than one interval of the same assembly;

and $\mathcal A$ is a supergenome if it is complete, irredundant and injective. For a supergenome and a fixed assembly $G$: the intervals $\{\pi_G(B)\}$ do not overlap, the natural interval order is a total order on each contig, each interval has at most one predecessor and one successor, and an interval adjacent to two others lies between them. The supergenome graph $\Gamma(\mathcal A)$ is the directed, edge-coloured multigraph on the blocks with an edge $(A, B)$ of colour $G$ whenever an interval of $A$ immediately precedes an interval of $B$ in assembly $G$. Each colour class is a disjoint union of directed paths, one per contig.

## Expansion

The three properties make each block a column-set that every assembly visits at most once, so the projection to one assembly is a set of disjoint, linearly ordered intervals and the colour classes of $\Gamma(\mathcal A)$ are paths. Common pipelines violate the axioms (progressive multi-alignments with a reference are typically not irredundant, and some are not injective), so a supergenome must be produced by refinement. A coordinate system for the supergenome is a linear order of the blocks; it should respect every betweenness relation induced by the individual assemblies, which leads to an ordering problem on $\Gamma(\mathcal A)$.

## Sources

- F. Gärtner, C. Höner zu Siederdissen, L. Müller and P. F. Stadler, "Coordinate systems for supergenomes", Algorithms for Molecular Biology 13 (2018) 15, <https://doi.org/10.1186/s13015-018-0133-4>, PMCID PMC6151955. Definitions 1–5 and Lemma 1.
