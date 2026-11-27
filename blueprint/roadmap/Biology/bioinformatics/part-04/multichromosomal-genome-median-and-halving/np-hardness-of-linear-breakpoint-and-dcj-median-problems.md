# NP-hardness of linear breakpoint and DCJ median problems

**Setting.** Genomes are sets of adjacencies between gene extremities on a gene set of size $n$, as in the multichromosomal model; the breakpoint distance is $d_{BP}(\Pi,\Gamma) = n - a(\Pi,\Gamma) - \tfrac12 e(\Pi,\Gamma)$ with $a$ the number of common adjacencies and $e$ the number of common telomeres. The breakpoint graph $BP(\Pi,\Gamma)$ has the gene extremities as vertices and one edge for each adjacency of $\Pi$ and of $\Gamma$; every component is a cycle or a path. With $c(\Pi,\Gamma)$ cycles and $p(\Pi,\Gamma)$ paths with an even number of edges, the double-cut-and-join distance is

$$d_{DCJ}(\Pi,\Gamma) = n - c(\Pi,\Gamma) - \tfrac12\, p(\Pi,\Gamma).$$

The median problem asks, for three genomes $\Pi_1,\Pi_2,\Pi_3$, for a genome $M$ minimizing $s(M) = \sum_i d(\Pi_i, M)$. For an all-duplicates genome $\Delta$, the double distance to an ordinary genome $\Pi$ is the minimum distance from $\Delta$ to a doubled genome $\Pi\oplus\Pi$; guided halving asks for $M$ minimizing $d(\Delta,M) + d(M,\Pi)$.

**Theorem.**
1. The breakpoint median problem is NP-hard when all genomes (inputs and median) must be multichromosomal linear, although it is polynomial for mixed or circular genomes.
2. Computing the DCJ double distance is NP-hard for multichromosomal mixed or circular genomes.
3. The DCJ median problem is NP-hard for multichromosomal genomes, even when all genomes are circular.
4. The DCJ guided halving problem is NP-complete for multichromosomal genomes.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)
- [Breakpoint median and halving by maximum-weight perfect matching](breakpoint-median-and-halving-by-maximum-weight-perfect-matching.md)

## Expansion

(1) A linear genome with at most two chromosomes reaching score $\le k$ exists iff a multichromosomal linear one does, which reduces the problem from the 2-chromosome breakpoint median; that problem encodes Hamiltonian cycle in a cubic-type graph, since a median meets the lower bound $s(M) \ge 2n - 1 + N_M - \lambda_2$ exactly when it uses every weight-2 adjacency and no weight-0 adjacency. (2) The DCJ double distance is reduced from breakpoint graph decomposition (maximum number of edge-disjoint alternating cycles in a 2-edge-coloured graph): the optimum number of cycles equals $2n - d(\Delta,\Pi) - w_2$, with $w_2$ the number of degree-2 vertices. (3) and (4) follow Caprara's unichromosomal median reduction: there is a genome with total distance at most $w_2 + 3w_4 - k$ iff the coloured graph has $k$ edge-disjoint alternating cycles, where $w_2,w_4$ count vertices of degree 2 and 4. The perfect-matching algorithm for the mixed breakpoint median still gives a lower bound in the linear case.

## Sources

- E. Tannier, C. Zheng, D. Sankoff, "Multichromosomal median and halving problems under different genomic distances", BMC Bioinformatics 10:120 (2009), Theorem 2 with Lemmas 1–2 and Claims 4–5, Theorem 3 (DCJ distance), Theorem 4 with Claim 6, Theorem 5 with Claim 7, Theorem 6, <https://doi.org/10.1186/1471-2105-10-120>, PMCID PMC2683817.
