# Underlying subwords and the underlying approach distance

**Priority and ties.** For distinct subwords $w, w'$, $w$ has priority over $w'$ ($w \to w'$) if $|w| > |w'|$, or $|w| = |w'|$ and the first occurrence of $w$ precedes that of $w'$; this is a total order. An occurrence $l$ of $w$ is **tied** to an occurrence $l'$ of $w'$ if the intervals $[l, l + |w| - 1]$ and $[l', l' + |w'| - 1]$ intersect and $w' \to w$; otherwise it is untied from $l'$.

**Definition 2 (underlying subwords).** A set $U_{s_1, s_2} \subseteq I_{s_1, s_2}$ of irredundant common subwords is underlying if (i) every $w \in U_{s_1, s_2}$ has at least two occurrences, one in $s_1$ and one in $s_2$, untied from all untied occurrences of the other subwords of $U_{s_1, s_2}$, and (ii) no $w \in I_{s_1, s_2} \setminus U_{s_1, s_2}$ has two such untied occurrences, one per sequence. The underlying set exists and is unique; the untied occurrences of its members are pairwise non-overlapping, so their total length is at most the sequence length.

**Complexity.** Given the generalized suffix tree, $U_{s_1, s_2}$ can be computed in $O((m + n) \log \min\{m, n\} \log\log \min\{m, n\})$ time and $O(m + n)$ space, because each position is re-examined at most $O(\log \min\{m, n\})$ times and each re-examination uses a weighted-ancestor query.

**Distance-like measure.** With $h_w^{s_1}$ the number of untied occurrences of $w$ in $s_1$ and $|s_1| = n$,

$$UA(s_1, s_2) = \frac{1}{n} \sum_{w \in U_{s_1, s_2}} h_w^{s_1} \frac{|w|(|w| + 1)}{2},$$

$$\overline{UA}(s_1, s_2) = \frac{\log_4 |s_2|}{UA(s_1, s_2)} - \frac{2 \log_4 |s_1|}{|s_1| + 1}, \qquad d_{UA}(s_1, s_2) = \frac{\overline{UA}(s_1, s_2) + \overline{UA}(s_2, s_1)}{2}.$$

The correction term uses $UA(s_1, s_1) = (|s_1| + 1)/2$, so $\overline{UA}(s_1, s_1) = 0$ and $d_{UA}(s, s) = 0$; $d_{UA}$ is symmetric and grows as the sequences diverge. Inversions and complements are handled by matching $s_1$ against the concatenation of $s_2$ with its reverse and its complement.

## Depends on

- [Irredundant common subwords and matching statistics](irredundant-common-subwords-and-matching-statistics.md)

## Expansion

Irredundant subwords may still overlap, so repetitive regions would be counted several times in matching-statistics scores. Processing irredundant subwords in priority order and keeping only occurrences not overlapped by a higher-priority one assigns every region to a single best pattern, the analogue of choosing one underlying motif per region. The $\log$ bound comes from the fact that a re-examined occurrence is forced to a prefix at most half as long as before. Each region contributes the triangular number of its length, as in the average common substring score, and the base-4 logarithm normalizes for the chance of random matches growing with the length of the second sequence.

## Sources

- M. Comin, D. Verzotto, "Alignment-free phylogeny of whole genomes using underlying subwords", Algorithms for Molecular Biology 7 (2012) 34, Methods (Definitions 1-2, Proposition 1, complexity analysis, distance-like measure), <https://doi.org/10.1186/1748-7188-7-34> (PMC3549825).
