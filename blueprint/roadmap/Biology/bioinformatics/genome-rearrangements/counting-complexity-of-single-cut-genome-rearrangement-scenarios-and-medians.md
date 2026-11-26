# Counting complexity of single-cut genome rearrangement scenarios and medians

**Genomes and operations.** A genome is an edge-labeled directed graph in which every label (gene) is unique and every vertex has total degree $1$ or $2$; it is a disjoint union of linear and circular chromosomes. Degree-$2$ vertices are *adjacencies* (two gene extremities joined) and degree-$1$ vertices are *telomeres*. The elementary operations are: (i) a *cut* of an adjacency $ab$ into telomeres $a$, $b$; (ii) a *join* of telomeres $a$, $b$ into an adjacency; (iii) a *cut-join*, replacing adjacency $ab$ and telomere $c$ by adjacency $ac$ and telomere $b$; (iv) a *double-cut-join*, replacing adjacencies $ab$, $cd$ by $ac$, $bd$. The Double Cut-and-Join (DCJ) model allows (i)–(iv), the **Single Cut or Join (SCoJ)** model allows (i)–(ii), and the **Single Cut-and-Join (SCaJ)** model allows (i)–(iii) (with restrictions on the operations allowed). For genomes $G_1, G_2$ on the same genes, $d(G_1,G_2)$ is the minimum number of operations, a *most parsimonious scenario* realizes it, and $\#\mathrm{MPS}(G_1,G_2)$ counts them. A *median* of $k \ge 3$ genomes minimizes $\sum_i d(G_i, G)$.

**Theorem.**
1. In the SCaJ model, **Pairwise Rearrangement**, which asks for $\#\mathrm{MPS}(G_1,G_2)$, is $\#\mathsf{P}$-complete under polynomial-time Turing reductions.
2. In the SCoJ model, **#Median**, counting all medians of a collection of genomes, is in $\mathsf{FL}$ (computable in logarithmic space). This improves the earlier polynomial-time bound.

The key enumeration step concerns adjacency graphs made only of *crowns* (even cycles of the adjacency graph $A(G_1,G_2)$). For crowns $C_1,\dots,C_q$ of sizes $c_1,\dots,c_q$, $\#\mathrm{MPS}$ has an explicit sum over set partitions of the crowns. Each term is a multinomial coefficient times $2^{d+q-3k}\prod_i c_i$ times rising-factorial factors, where $k$ is the number of parts. For a single non-trivial crown of size $c$, the number of sorting traces is $c\cdot 2^{c-1}$.

So exact counting of parsimonious histories is tractable for SCoJ (pairwise counting is already in $\mathsf{FP}$), intractable for SCaJ, and conjectured $\#\mathsf{P}$-complete for reversals and DCJ.

## Expansion

The adjacency graph $A(G_1,G_2)$ has one vertex per adjacency or telomere of each genome and an edge for each shared extremity. Its components are paths ($W$-, $M$-, $N$-shaped) and even cycles (crowns), and each operation on $G_1$ acts locally on these components. Sorting scenarios interleave independent sorting traces of the components. Under SCaJ, the cut-join operation lets crowns be sorted jointly, which produces the partition sum. Hardness is shown by a polynomial-time Turing reduction from Multiset-Equal-Partition (itself shown $\#\mathsf{P}$-hard from Multiset-Partition): crown sizes encode the multiset, and the partition sum in the all-crowns formula exposes the count of equal partitions. For SCoJ, the distance is governed by the symmetric difference of the adjacency sets, and the median-counting argument is refined so that it runs in logarithmic space.

## Sources

- Lora Bailey, Heather Smith Blake, Garner Cochran, Nathan Fox, Michael Levet, Reem Mahmoud, Elizabeth Matson, Inne Singgih, Grace Stadnyk, Xinyi Wang and Alexander Wiedemann, "Complexity and Enumeration in Models of Genome Rearrangement", arXiv:2305.01851 (2023), Section 1 (Theorems 1.1 and 1.3), Section 2 (Definitions 2.1–2.4), Section 3 (Theorem 3.1 on all-crowns sorting scenarios), Sections 4–5, <https://doi.org/10.48550/arXiv.2305.01851>.
