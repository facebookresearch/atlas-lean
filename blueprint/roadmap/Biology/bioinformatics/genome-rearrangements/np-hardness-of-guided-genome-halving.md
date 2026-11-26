# NP-hardness of guided genome halving

Represent a genome on genes $\{1, \dots, n\}$ as a set of $\chi$ chromosomes, each a string of signed genes, every gene appearing exactly once. Two genomes $G, H$ with the same number $\chi$ of chromosomes share an *adjacency* when two signed genes are consecutive (in either reading direction) in both, counting chromosome ends as adjacencies with a telomere. Their *breakpoint distance* is

$$d_B(G, H) = n + \chi - \#\{\text{shared adjacencies}\}.$$

A *doubled genome* $T$ carries two copies $i^1, i^2$ of each gene $i$, the copies being indistinguishable. A *doubled ancestor* $A' \oplus A''$ consists of $2\chi$ chromosomes, where $A'$ contains exactly one copy of each gene and $A''$ is $A'$ with every copy swapped for its twin; $A$ denotes $A'$ with copy labels erased.

**Guided genome halving (GGH).** Given a doubled genome $T$ and an ordinary outgroup genome $R$, find a doubled ancestor minimizing

$$d_B(A' \oplus A'', T) + d_B(A, R).$$

**Theorem.** GGH with one outgroup under the breakpoint distance is NP-hard. Indeed, for genomes $P, Q, R$ on the same genes, set $T = P^1 \oplus Q^2$ (copy label $1$ on every gene of $P$, label $2$ on every gene of $Q$). Then the halved genome $A$ of any optimal GGH solution for $(T, R)$ minimizes $d_B(A,P) + d_B(A,Q) + d_B(A,R)$, i.e. it solves the breakpoint median problem for $P, Q, R$, which is NP-hard.

## Depends on

- [Greedy breakpoint algorithm for sorting by reversals](greedy-breakpoint-bound-for-unsigned-sorting-by-reversals.md)

## Expansion

Every adjacency of $T = P^1 \oplus Q^2$ joins two genes with the same copy label. Hence replacing an optimal $A' \oplus A''$ by $A^1 \oplus A^2$ (all labels $1$ in the first half, all $2$ in the second) keeps every adjacency shared with $T$ and does not change the outgroup term, so an optimal solution of this labelled form exists (Lemma 1). For such solutions the shared adjacencies split into those of $A^1$ with $P^1$ and those of $A^2$ with $Q^2$, giving $d_B(A^1 \oplus A^2, T) = d_B(A, P) + d_B(A, Q)$ (Lemma 2). The GGH objective therefore equals the breakpoint median objective. A genome $A^*$ with a smaller median score would give a GGH solution with a smaller objective, a contradiction. In contrast, genomic distance and unguided genome halving are computable in linear time. The hardness motivates heuristics: guided halving algorithms steer the arbitrary choices of the linear-time halving algorithm toward the outgroups and then improve the result by local search along trajectories to median solutions. They were applied to reconstruct the pre-doubling ancestor of baker's yeast and *Candida glabrata*.

## Sources

- C. Zheng, Q. Zhu, Z. Adam, D. Sankoff, "Guided genome halving: hardness, heuristics and the history of the Hemiascomycetes", *Bioinformatics* (2008), Section 2 (genomes, breakpoint distance, genome halving, problem statement) and Section 5 (reduction from the breakpoint median problem, Lemmas 1–2 and Theorem 1), <https://doi.org/10.1093/bioinformatics/btn146> (PMC2718624).
