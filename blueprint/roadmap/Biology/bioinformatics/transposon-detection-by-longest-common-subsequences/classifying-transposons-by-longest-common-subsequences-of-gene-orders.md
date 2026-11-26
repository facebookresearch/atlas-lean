# Classifying transposons by longest common subsequences of gene orders

**Setup.** Several individuals of a species carry the same $n$ genes in possibly different orders; genes that have moved are candidate transposons. Treating the conserved order as a longest common subsequence (LCS) of the $m$ gene sequences, a gene is

- a **proper transposon** if it lies in no LCS,
- a **non-transposon** if it lies in every LCS,
- a **quasi-transposon** if it lies in some but not all LCSs.

Four scenarios arise: linear or circular sequences (circular ones may be rotated), without or with duplicated genes. With duplicates, only subsequences containing all or none of the copies of each gene count, and length is measured in genes.

**Linear sequences without duplicates (polynomial algorithm).** Add sentinels $0$ at the head and $n+1$ at the tail of every sequence. The **auxiliary graph** $\mathcal{G}$ has a vertex for each gene and an arc $g_i \to g_j$ exactly when $g_i$ precedes $g_j$ in all $m$ sequences. It is acyclic, and directed paths from $0$ to $n+1$ correspond bijectively to common subsequences, so an LCS is a longest $0 \to n+1$ path. Let $F_+(g)$ be the length of a longest path from $g$ to $n+1$ and $F_-(g)$ that of a longest path from $0$ to $g$, computed by dynamic programming,

$$
F_+(g_i) = 1 + \max_{g_i \to g_j} F_+(g_j), \qquad F_-(g_i) = 1 + \max_{g_j \to g_i} F_-(g_j),
$$

and let $\mathcal{L}_0$ be one longest path, of length $F_+(0)$. Then $F_+(g) + F_-(g)$ is the length of a longest path through $g$. A gene off $\mathcal{L}_0$ is a proper transposon if $F_+(g) + F_-(g) < F_+(0)$ and a quasi-transposon if equality holds. A gene on $\mathcal{L}_0$ is a non-transposon if and only if it lies on every longest path $\mathcal{L}_g$ built through the quasi-transposons $g$. The whole classification runs in polynomial time; building $\mathcal{G}$ from the $m$ sequences costs $O(mn^2)$.

**Lemma (pairing of quasi-transposons).** In the linear duplicate-free scenario, every quasi-transposon $g_i$ has a partner quasi-transposon $g_j$ such that no LCS contains both.

**Lemma (cutting circular sequences).** For circular sequences without duplicates, cutting all sequences at a quasi-transposon $g_p$ gives linear sequences in which every circular proper transposon is still a proper transposon and every circular non-transposon is still a non-transposon. This reduces the circular case to linear instances.

**Proposition (duplicates make the problem NP-hard).** For linear sequences with duplicated genes, finding an LCS (counting whole genes) is NP-hard. Every undirected graph $\mathcal{G}$ can be encoded by two gene sequences whose common subsequences correspond bijectively to the cliques of $\mathcal{G}$, so an LCS gives a maximum clique.

## Expansion

Without duplicates, "precedes in every sequence" is a strict partial order, so $\mathcal{G}$ is a DAG and longest paths are computable in linear time in its size. The test $F_+(g) + F_-(g)$ against the global maximum decides whether $g$ lies on some optimal path. With duplicates the order relation between genes is no longer transitive, because copies interleave. In the reduction, two genes are made comparable in the same direction in both sequences exactly when they are adjacent in the graph, by placing copies so that non-adjacent pairs appear in conflicting orders. A set of genes is then a common subsequence exactly when it is pairwise compatible, that is, a clique, so the problem inherits the NP-hardness of maximum clique. In practice, LCS-based classification separates genes that certainly moved (proper transposons) from those whose status is ambiguous because several equally parsimonious conserved orders exist (quasi-transposons).

## Sources

- Yue Wang, "Algorithms for determining transposons in gene sequences", arXiv (2015), Section 2 (Definition 1 and the four scenarios), Section 3 (auxiliary graph, Definitions 2–4, longest-path algorithm, Lemma 1), Section 4 (Lemma 2, Conjecture 1), Section 5 (Lemmas 3–4, Proposition 1), <https://doi.org/10.48550/arXiv.1506.02424>.
