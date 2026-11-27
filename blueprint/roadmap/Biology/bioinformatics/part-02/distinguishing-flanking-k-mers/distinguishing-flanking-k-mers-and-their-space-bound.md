# Distinguishing flanking k-mers and their space bound

Fix $k$ and the alphabet $\Sigma = \{A, C, G, T\}$. Let $U$ be the compacted de Bruijn graph (dBG) of the target sequences (for example mature and nascent transcripts), with $N_k$ distinct $k$-mers, and let the **D-list** $D$ be a set of background sequences (by default the genome) with $M_k$ distinct $k$-mers. For every maximal substring of length at least $k$ occurring in both $D$ and the targets, the first $k$-mer of $D$ immediately upstream and the first immediately downstream of it that are not in the dBG are its **distinguishing flanking $k$-mers (DFKs)**. DFKs are added to the index as uncoloured vertices: a read whose pseudoalignment encounters a DFK is masked rather than assigned to a target.

**Lemma.** The number of DFKs is at most $\min(8N_k, M_k)$ (each dBG $k$-mer has at most four candidate flanking $k$-mers on each side, and at most three on a side where it has a dBG neighbour), so their worst-case space is $O(\min(N_k, M_k))$.

**Read classification.** With an index containing both mature transcripts and nascent (intron-retaining) transcripts, plus DFKs from the genome, each read compatible with a gene is classified as **mature** (compatible only with mature targets, e.g. spanning an exon–exon junction), **nascent** (compatible only with nascent targets, e.g. touching an intron) or **ambiguous** (compatible with both, e.g. entirely exonic); counts are then combined as mature + ambiguous for cytoplasmic (cell) RNA, nascent + ambiguous for nuclear RNA, or all three for total RNA.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

Each $k$-mer $s$ of the dBG has at most $|\Sigma| = 4$ possible successors and $4$ predecessors in any sequence. A DFK adjacent to $s$ must lie in $D$ but not in the dBG, and if $s$ is extended at all within the dBG on that side, at most $|\Sigma| - 1 = 3$ of the $4$ neighbours can be DFKs; two sides give at most $6$ per dBG $k$-mer, while every DFK is also a distinct $k$-mer of $D$. Because a read from outside the targets that shares only part of its sequence with a transcript must cross one of these boundaries, its $k$-mers hit a DFK, which blocks the mismapping that a transcript-only index would produce, while the index stays far smaller than including the whole genome as a decoy.

## Sources

- D. K. Sullivan, K. E. Hjörleifsson, N. P. Swarna, C. Oakes, G. Holley, P. Melsted, L. Pachter, "Accurate quantification of nascent and mature RNAs from single-cell and single-nucleus RNA-seq", Nucleic Acids Research 53(1) (2025) gkae1137, Materials and methods ("The D-list", "Generating DFKs", Algorithm 1, Lemma 1) and Figure 2, <https://doi.org/10.1093/nar/gkae1137>, PMCID PMC11724275.
