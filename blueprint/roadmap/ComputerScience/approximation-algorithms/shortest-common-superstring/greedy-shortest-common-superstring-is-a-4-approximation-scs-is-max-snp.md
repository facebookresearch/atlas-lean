# Greedy superstring approximation and hardness of the shortest superstring

For a finite nonempty set $S$ of nonempty strings over a finite alphabet, no one a substring of another, let $\mathrm{OPT}(S)$ be the length of a shortest common superstring. Following Blum, Jiang, Li, Tromp and Yannakakis (1994, Section 2), the overlap $\mathrm{ov}(s, t)$ of strings $s$ and $t$, not necessarily distinct, is the length of the longest $v$ with $s = uv$ and $t = vw$ for nonempty strings $u$ and $w$. For distinct $s, t \in S$ this is the [overlap](../../../Biology/not-yet-classified/string-overlap/overlap.md) (the length of the largest suffix of $s$ that is a prefix of $t$), since an overlap of full length would make one string a substring of the other, and merging $s$ and $t$ along it is their [merge along the overlap](../../../Biology/not-yet-classified/string-overlap/merge.md). On the diagonal, $\mathrm{ov}(s, s)$ is the length of the longest proper border of $s$ (a proper prefix that is also a suffix), zero if there is none, not the full length $|s|$. The overlap graph of $S$ is the complete directed graph on $S$, self-loops included, with edge weights $\mathrm{ov}(s, t)$, and the prefix (distance) graph $G_S$ gives the same edges the weights $|s| - \mathrm{ov}(s, t)$; a cycle cover of $G_S$ of minimum total weight is an optimal cycle cover. They prove four statements: the greedy algorithm GREEDY, which repeatedly replaces two distinct strings with maximum overlap by their merge, produces a superstring of length at most $4\,\mathrm{OPT}(S)$ (Theorem 12); the variant MGREEDY, which repeatedly chooses $s$ and $t$ with maximum overlap in the overlap graph, possibly $s = t$, merges them when $s \ne t$ and sets $s$ aside when $s = t$, constructs an optimal cycle cover of $G_S$ (Theorem 10), and concatenating the strings of the cycles of an optimal cover costs at most $4\,\mathrm{OPT}(S)$ (Theorem 8), so MGREEDY also achieves $4\,\mathrm{OPT}(S)$; TGREEDY, which runs GREEDY on the strings MGREEDY sets aside instead of concatenating them, produces a superstring of length at most $3\,\mathrm{OPT}(S)$ (Theorem 11); and the shortest superstring problem is MAX SNP-hard (Theorem 18), by reduction from the traveling salesman problem with distances $1$ and $2$. The proper self-overlap matters for MGREEDY: for the eight words of length $8$ with one letter $b$ and seven letters $a$, a full self-overlap of $8$ would exceed every overlap between distinct words, so MGREEDY would concatenate all eight words (length $64$), while $a^7ba^7$ of length $15$ contains them all, so $4\,\mathrm{OPT}(S) \le 60$.

## Depends on

- [Largest overlap of two lists](../../../Biology/not-yet-classified/string-overlap/overlap.md)
- [Merge along the overlap](../../../Biology/not-yet-classified/string-overlap/merge.md)

## Expansion

1. Definitions: overlaps with nonempty remainders (the longest proper border on the diagonal), prefixes, the overlap graph and the distance (prefix) graph with self-loops, cycle covers, and the reduction to substring-free sets.
2. Theorem 8: the lower bound $\mathrm{CYC}(G_S) \le \mathrm{OPT}(S)$ and the bound for concatenating cycles, using the overlap lemma for strings in different cycles.
3. Theorem 10: the greedy choice of edges by overlap in the overlap graph, self-loops weighted by proper self-overlaps, yields an optimal assignment for these graphs (the Monge property; compare Hoffman 1963).
4. Theorems 11 and 12: the bounds for TGREEDY, run on the cycles MGREEDY forms in the same graph, and GREEDY.
5. Theorem 18: the MAX SNP-hardness reduction.

## Sources

- A. Blum, T. Jiang, M. Li, J. Tromp and M. Yannakakis, Linear approximation of shortest superstrings, J. ACM 41 (1994), 630–647, Theorems 8, 10, 11, 12 and 18. <https://doi.org/10.1145/179812.179818>
