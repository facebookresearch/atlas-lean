# Two-of-(k+2) non-overlapping q-gram filter

**Setting.** Let $s$ be a reference genome with an inverted index listing, for every $q$-gram $g$, the positions where $g$ occurs in $s$. For a read $r$ and a $q$-gram $g$ occurring at offset $o$ in $r$, the *normalized inverted list* $I_n(g)$ is the set of positions $\ell-o$ for $\ell$ in the inverted list of $g$, i.e. the candidate start positions of $r$ consistent with that occurrence. A mapping of $r$ at start position $\ell$ with Hamming distance at most $k$ is a position where the substring of $s$ of length $|r|$ starting at $\ell$ differs from $r$ in at most $k$ bases.

**Classical prefix filter.** If $g_1,\dots,g_{k+1}$ are non-overlapping $q$-grams of $r$, every mapping position lies in $\bigcup_{i=1}^{k+1}I_n(g_i)$.

**Lemma (additional prefix).** If $g_1,\dots,g_{k+2}$ are non-overlapping $q$-grams of $r$, every mapping position of $r$ within Hamming distance $k$ lies in at least two of the lists $I_n(g_1),\dots,I_n(g_{k+2})$; equivalently, the candidate set can be taken as

$$\bigcap_{\substack{S\subseteq\{1,\dots,k+2\}\\|S|=k+1}}\ \bigcup_{i\in S}I_n(g_i)\;=\;\bigcup_{1\le i<j\le k+2}\big(I_n(g_i)\cap I_n(g_j)\big),$$

which is contained in the classical candidate set of any $k+1$ of the $q$-grams.

## Expansion

Because the $q$-grams do not overlap, each mismatch destroys at most one of them, so with at most $k$ mismatches at least $(k+2)-k=2$ of them occur unchanged at the aligned position. Equivalently, applying the $k+1$ pigeonhole filter to each of the $k+2$ subsets of size $k+1$ and intersecting the results loses nothing; distributivity, absorption and idempotence of set operations turn that intersection of unions into the union of pairwise intersections. The extra $q$-gram costs one more list lookup but removes positions supported by a single seed, which dominate the candidates in repetitive regions. Insertions and deletions shift later $q$-grams relative to the read, so the edit-distance version needs adjusted normalization.

## Depends on

- [q-gram (seed) filtering lemma for approximate matching](../../q-gram-filtering-lemma-for-approximate-matching.md)

## Sources

- J. Kim, C. Li, X. Xie, "Improving read mapping using additional prefix grams", *BMC Bioinformatics* 15:42 (2014), Lemma 1 and the section on candidate generation, <https://doi.org/10.1186/1471-2105-15-42>, PMCID: PMC3927682.
