# Incomplete multi-colour breakpoint graph

Let $\mathcal{B}$ be a set of synteny blocks, let $P_1, \dots, P_k$ be reference genomes written as sequences (or cyclic sequences) of signed blocks, and let the target assembly $A$ be a set of contigs, each a sequence of signed blocks. Assume every block of $\mathcal{B}$ occurs exactly once in $A$ and at most once in each $P_c$ (blocks absent from $A$ and repeated blocks are filtered out first). The incomplete multi-colour breakpoint graph $BG(A, P_1, \dots, P_k) = (V, E)$ has vertex set

$$V = \{\, b^{h}, b^{t} : b \in \mathcal{B} \,\},$$

the head and tail of each block, and an undirected edge of colour $c \in \{\mathrm{red}, P_1, \dots, P_k\}$ between two block extremities whenever they are adjacent in genome $c$ (red for the assembly).

Properties:

1. every vertex has at most one incident edge of each colour;
2. if the target genome were complete, its red edges would form a perfect matching of $V$ (circular chromosomes), or a matching covering all vertices except the two ends of each linear chromosome;
3. in the fragmented assembly, the vertices with no red edge are exactly the block extremities at contig ends, and recovering the target amounts to completing the red matching on those vertices.

## Expansion

Property 1 holds because each block extremity has at most one neighbour in a genome where the block occurs once. Property 2 holds because, in a complete genome, every block end is adjacent to exactly one other block end along its chromosome. The graph generalizes the classical breakpoint graph of complete genomes to a fragmented one. Candidate red edges at a contig end are the reference-coloured edges incident to that vertex, so the reference adjacencies propose joins and the phylogeny ranks them.

## Sources

- M. Kolmogorov, B. Raney, B. Paten, S. Pham, "Ragout—a reference-assisted assembly tool for bacterial genomes", Bioinformatics 30(12) (2014) i302–i309, section 2.2.1 ("Incomplete multi-color breakpoint graphs"), <https://doi.org/10.1093/bioinformatics/btu280> (PMC4058940).
