# Intermediate genomes are non-crossing chord diagrams in the breakpoint graph

**Setting.** Genomes $A$ and $B$ on the same $n$ genes are sets of adjacencies between gene extremities, and $d(\cdot,\cdot)$ is the DCJ distance. In the circular breakpoint graph $BP(A,B)$ (with telomere vertices added so that every component is an alternating cycle of $A$-edges and $B$-edges, an *$AB$-cycle*), a DCJ applied to one genome removes two of its edges and reconnects the four endpoints differently, and $d(A,B) = n - c$, where $c$ is the number of $AB$-cycles and $n$ counts genes including the added telomere pairs. A genome $M$ is an *intermediate genome* of $A$ and $B$ if it occurs in some optimal DCJ sorting scenario $A = M_0, M_1, \dots, M_k = B$ with $k = d(A,B)$, equivalently $d(A,M) + d(M,B) = d(A,B)$. An *independent component scenario* is one in which every DCJ acts within a single component of the breakpoint graph.

**Theorem.** A genome $M$ is an intermediate genome of $A$ and $B$ in an independent component scenario if and only if every edge (adjacency) of $M$ is a chord inside an $AB$-cycle of $BP(A,B)$, no two such chords cross, and the edges of $M$ cover all vertices of $BP(A,B)$.

**Counting.** An $AB$-cycle with $2n$ vertices admits exactly the Catalan number $C_n = \frac{1}{n+1}\binom{2n}{n}$ perfect non-crossing chord diagrams, so the number of such intermediate genomes is

$$IG(A,B) = \prod_{K \in BP(A,B)} C_{|K|/2},$$

the product over the $AB$-cycles $K$ with $|K|$ vertices.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

*Necessity.* If a DCJ moved an intermediate genome $M$ strictly closer to $A$ without moving it away from $B$, the triangle inequality $d(A,B) \le d(A,M') + d(M',B) < d(A,M) + d(M,B) = d(A,B)$ would fail (Lemma 1). An optimal DCJ splits a cycle into two, and the two new edges never cross; crossing chords would allow a DCJ that uncrosses them and splits one $AM$-cycle without merging any $BM$-cycles, contradicting Lemma 1 (Lemma 2). *Sufficiency.* By induction on the number of chords, an $AB$-cycle with $2n$ vertices and $n$ non-crossing covering $M$-edges yields $AM$- and $BM$-cycle counts summing to $n+1$ (Lemma 3). Summing over the $c$ cycles gives $c_{AM} + c_{BM} = n + c$, hence $d(A,M) + d(M,B) = (n - c_{AM}) + (n - c_{BM}) = n - c = d(A,B)$ (Lemma 4). Choosing an intermediate genome therefore amounts to choosing independently, in each cycle, one non-crossing perfect matching of its vertices, which gives the Catalan product.

## Sources

- P. Feijão, "Reconstruction of ancestral gene orders using intermediate genomes", BMC Bioinformatics 16 (Suppl. 14) (2015) S3, Methods (circular breakpoint graph, Theorem 1, Lemmas 1–4, Eq. (2)), <https://doi.org/10.1186/1471-2105-16-S14-S3>, PMCID PMC4602182.
