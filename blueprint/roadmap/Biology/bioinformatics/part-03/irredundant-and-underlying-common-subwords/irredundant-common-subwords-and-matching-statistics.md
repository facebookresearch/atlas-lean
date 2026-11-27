# Irredundant common subwords and matching statistics

**Setting.** Let $s_1, s_2$ be strings with $|s_1| = n$ and $|s_2| = m$. The **matching statistics** of $s_1$ against $s_2$ is the vector $l_{s_1}(i)$, $1 \le i \le n$, where $l_{s_1}(i)$ is the length of the longest substring of $s_1$ starting at position $i$ that also occurs in $s_2$. A common subword $w$ (a string occurring in both) **covers** an occurrence of another common subword when the latter lies inside an occurrence of $w$.

**Definition 1 (irredundant common subword).** A common subword $w$ of $s_1$ and $s_2$ is irredundant if at least one of its occurrences in $s_1$ or $s_2$ is not covered by other common subwords; otherwise it is redundant. Let $I_{s_1, s_2}$ be the set of irredundant common subwords.

Since $I_{s_1, s_2}$ is a subset of the maximal common subwords, $|I_{s_1, s_2}| \le m + n$, and $I_{s_1, s_2}$ can be extracted from the generalized suffix tree of $s_1$ and $s_2$ in time and space linear in $m + n$.

**Proposition 1.** The matching statistics $l_{s_1}(i)$ can be computed by combining only the irredundant common subwords of $s_1$ and $s_2$: superimposing, on every occurrence $k$ of every $w \in I_{s_1, s_2}$ in $s_1$, the score vector $l_w[j] = |w| - j + 1$, one has

$$l_{s_1}(i) = \max\{ l_w[j] : w \in I_{s_1, s_2}, \ k + j = i, \ k \text{ an occurrence of } w \text{ in } s_1 \},$$

and the irredundant common subwords suffice. Moreover, no irredundant subword with an occurrence in $s_1$ that is not covered by other common subwords can be omitted.

## Proof depends on

- [Suffix tree](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-tree/suffix-tree.md)

## Expansion

Every occurrence of a common subword is either itself an occurrence of an irredundant subword or is covered by one, so the superimposed suffix-length scores already reach the longest match at each position. Conversely, if an irredundant $w$ has an uncovered occurrence $i$ in $s_1$, then $l_{s_1}(i) = |w|$ is witnessed by $w$ alone, so $w$ is necessary. An irredundant subword whose uncovered occurrences all lie in $s_2$ may be omitted: for $s_1 = xab$ and $s_2 = abzxab$, $ab$ is irredundant through its occurrence at $s_2[1..2]$, but $l_{s_1} = (3, 2, 1)$ comes from $xab$ alone. This is the reason the average common substring score, built from matching statistics, can be decomposed into a linear number of patterns, which is the starting point for removing overlapping (overcounted) matches.

## Sources

- M. Comin, D. Verzotto, "Alignment-free phylogeny of whole genomes using underlying subwords", Algorithms for Molecular Biology 7 (2012) 34, Methods (Definitions 1-2, Proposition 1, complexity analysis, distance-like measure), <https://doi.org/10.1186/1748-7188-7-34> (PMC3549825).
