# Coverage-preserving de Bruijn and overlap graphs

Model a genome as a set of circular strings over $\{A,C,G,T\}$, each of length at most $\phi$, and let $R$ be an error-free multiset of reads, each a substring of some chromosome. Fix integers $l_1 > l_2 \ge 1$. A circular string $z$ is **sufficiently covered** if every interval of length $l_1 - l_2$ of $z$ contains the start of a substring of $z$ of length at least $l_1$ that equals a read of $R$. Let $C(R, l_1, l_2, \phi)$ be the set of all sufficiently covered circular strings of length at most $\phi$; the true genome is a subset of it. An assembly graph $G$ (vertices labeled by strings, arcs by suffix-prefix overlaps) **spells** a circular string if some closed walk concatenates the vertex labels, without repeating overlaps, into that string; $G$ is **coverage-preserving** if it spells every string of $C(R, l_1, l_2, \phi)$.

Let $B_k(R)$ be the node-centric de Bruijn graph on the $k$-mers of $R$, and $O_k(R)$ the overlap multigraph whose vertices are reads and whose arcs are all suffix-prefix overlaps of length at least $k$.

**Theorem 1.** $B_k(R)$ is coverage-preserving for every $k \le l_2 + 1$.

**Theorem 2.** $O_k(R)$ is coverage-preserving for every $k \le l_2$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

Decreasing $k$ only adds arcs, so it suffices to treat $k = l_2 + 1$ (de Bruijn) and $k = l_2$ (overlap). For the de Bruijn graph, if some $k$-mer of $z$ were missing from the reads, take the first such position $i$; the length-$(l_1 - l_2)$ interval ending at $i$ contains the start of a read-matching substring of length at least $l_1$, which then contains that $k$-mer, a contradiction; with all $k$-mers present, the walk through consecutive $k$-mers spells $z$. For the overlap graph, for each interval $A_i$ pick the earliest read-matching substring $z[A_i.s : A_i.e]$ of length at least $l_1$ and extract a subsequence $T_1, \dots, T_p$ with strictly increasing starts and ends. Consecutive chosen substrings overlap by at least $l_2$ (Lemma 1: $A_i.e \ge A_{i+1}.s + l_2 - 1$; Lemma 3 transfers this to the subsequence), the subsequence has length at least two (Lemma 2), and the last read overlaps the first by at least $l_2$ around the circle (Lemma 4). Hence the reads $T_1.r, \dots, T_p.r, T_1.r$ form a closed walk in $O_{l_2}(R)$ whose non-overlapping prefixes spell $z$.

## Sources

- C. Jain, "Coverage-preserving sparsification of overlap graphs for long-read assembly", Bioinformatics (2023), Section 2.3 (coverage assumption and Definition), Section 3 (Theorems 1 and 2, Lemmas 1-4, Observation), Section 4 (Lemmas 5-8). <https://doi.org/10.1093/bioinformatics/btad124> (PMC10132763)
