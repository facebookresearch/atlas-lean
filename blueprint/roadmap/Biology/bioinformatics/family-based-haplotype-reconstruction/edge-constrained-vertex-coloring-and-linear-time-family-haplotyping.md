# Edge-constrained vertex colouring and linear-time family haplotyping

**ECVC problem.** Let $G=(V,E)$ be a finite multigraph, $C$ a set of colours and $L:E\to\binom{C}{2}_{\text{multi}}$ an *edge constraint list* assigning to each edge a multiset of two colours. A solution is a vertex colouring $\phi:V\to C$ such that for every edge $e=\{v,w\}$ the multiset $\{\phi(v),\phi(w)\}$ equals $L(e)$. For $v\in V$ let

$$\mathcal I_v=\bigcap_{e\ni v}\operatorname{supp}L(e)$$

be the set of colours allowed at $v$; every solution has $\phi(v)\in\mathcal I_v$.

**Theorem.**
1. If $\mathcal I_v=\varnothing$ for some $v$, there is no solution.
2. For connected $G$: if $|\mathcal I_v|=1$ for some $v$, there is at most one solution; if $|\mathcal I_v|=2$ for all $v$, then $L$ is constant with two distinct colours, so solutions are proper 2-colourings and there are exactly two solutions if $G$ is bipartite and none otherwise.
3. If $G$ contains an odd cycle on which $L$ is constant with two distinct colours, there is no solution.
4. A generating set of all solutions, or a certificate that none exists, can be found in time $O(|E|)$; consequently $N$ ECVC problems on the same multigraph are solved in time $O(N|E|)$.

**Haplotype reconstruction.** In a pedigree with sequenced members, fix a genomic interval $\mathcal I$ on which the family is recombination-free (identity-by-descent, estimated from sparse linkage markers, is constant on $\mathcal I$). The *family-haplotype multigraph* has one vertex per founder haplotype carried by a sequenced individual and one edge per sequenced individual joining its two haplotypes. At marker $M_k$ in $\mathcal I$, colours are alleles and $L_k(e)$ is the unordered genotype of individual $e$. Then a unique ECVC solution reconstructs every haplotype's allele at $M_k$; no solution certifies a genotyping error or mutation; two solutions on a component leave its haplotypes undetermined at $M_k$ (on large components this flags a marker with excess heterozygosity). Hence family haplotypes on recombination-free intervals are reconstructed in time linear in both family size and number of markers.

## Expansion

Once one vertex of a connected component has a forced colour, every edge forces its other endpoint to the remaining element of its constraint multiset, so propagation along a spanning tree determines the colouring and the remaining edges only need to be checked; this gives parts 1–2 and the linear running time. If every vertex has two candidate colours, all incident constraints have the same support and the problem is 2-colouring, which fails exactly on odd cycles. The genomic encoding works because without recombination each child inherits whole founder haplotypes, so each genotype is the unordered pair of alleles of two vertices of the multigraph.

## Sources

- Jason A. Anema, Laura Escobar, "A graph coloring approach to family-based haplotype reconstruction", arXiv:2110.07101 (2021), Definition 2.1, Lemma 2.2, Propositions 2.3 and 2.5, and Section 3.1 (ECVC problems for haplotype reconstruction on recombination-free intervals), <https://doi.org/10.48550/arXiv.2110.07101>.
