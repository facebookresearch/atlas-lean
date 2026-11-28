# DCJ-indel distance and indel-potential of singular genomes

**Setting.** A genome is a set of linear or circular chromosomes over oriented markers. For genomes $A, B$ let $\mathcal{G}$ be the set of common markers and $\mathcal{U}$ the exclusive markers; the genomes are *singular* if every common marker occurs once in each. The DCJ-indel distance $d_{\mathrm{DCJ}}^{\mathrm{id}}(A,B)$ is the minimum number of double-cut-and-join operations and indels (insertion or deletion of a contiguous block of exclusive markers) transforming $A$ into $B$.

**Relational diagram.** $R(A,B)$ has a vertex for each extremity of each marker occurrence, adjacency edges for adjacencies of $A$ and of $B$, extremity edges joining the same extremity of a common marker in $A$ and $B$, and an indel edge joining the two extremities of each maximal block of exclusive markers. Its components are cycles and paths ($AA$-, $BB$- or $AB$-paths, by the genomes of their endpoints). A *run* of a component $C$ is a maximal subpath whose first and last edges are indel edges and whose indel edges all belong to the same genome; let $\Lambda(C)$ be the number of runs. The *indel-potential* is

$$\lambda(C) = \begin{cases} 0, & \Lambda(C) = 0,\\ \big\lceil (\Lambda(C)+1)/2 \big\rceil, & \Lambda(C) \ge 1.\end{cases}$$

**Theorem.** Let $c$ be the number of $AB$-cycles (cycles with at least two extremity edges; circular singletons, cycles made only of indel and adjacency edges of one genome, are not counted) and $i$ the number of $AB$-paths of $R(A,B)$.

1. (Upper bound) $d_{\mathrm{DCJ}}^{\mathrm{id}}(A,B) \le |\mathcal{G}| - c - \tfrac{i}{2} + \sum_{C}\lambda(C)$.
2. (Circular genomes) If $A, B$ are circular, the bound is tight: $d_{\mathrm{DCJ}}^{\mathrm{id}}(A,B) = |\mathcal{G}| - c + \sum_C \lambda(C)$.
3. (Linear genomes) In general

    $$d_{\mathrm{DCJ}}^{\mathrm{id}}(A,B) = |\mathcal{G}| - c - \frac{i}{2} + \sum_C\lambda(C) - \delta,$$

    where $\delta = 2P + 3Q + 2T + S + 2M + N$ counts the deductions achieved by greedily maximizing six families $P, Q, T, S, M, N$ of chained *deducting recombinations* (DCJs acting on two paths whose DCJ-indel cost $\Delta d$ is negative).

4. (Canonical genomes) With no exclusive markers, $\lambda \equiv 0$ and $d_{\mathrm{DCJ}}^{\mathrm{id}}(A,B) = |\mathcal{G}| - c - i/2$, the classical DCJ distance.

For a cycle, $\Lambda(C) \in \{0, 1\} \cup 2\mathbb{N}$, so $\lambda(C) = \Lambda(C)$ if $\Lambda(C) \le 1$ and $\lambda(C) = \Lambda(C)/2 + 1$ if $\Lambda(C) \ge 2$.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

Sorting each component separately with optimal DCJs closes cycles while merging runs (two runs become one) and accumulating them (a run that alternates only with adjacency edges is removed by one indel); the minimum number of indels left from $C$ is $\lambda(C)$, which gives the upper bound. Neutral or counter-optimal DCJs on one component never lower the combined cost $\Delta d = \|\rho\| + \Delta\lambda$, so the bound is tight when every component is a cycle. On linear genomes a recombination cuts two different paths; only path types matter through the parity of their number of runs and the genome of the first run, and an exhaustive table of such types yields the chained groups whose sources are original paths, so the greedy count $\delta$ is optimal.

## Sources

- L. Bohnenkämper, M. D. V. Braga, D. Doerr, J. Stoye, "Computing the rearrangement distance of natural genomes", Journal of Computational Biology 28 (2021), Section 3 (indel-potential, Lemma 1, the circular formula and Theorem 1) and Section 6 (indel-potential of cycles), <https://doi.org/10.1089/cmb.2020.0434>, PMCID PMC8082732.
