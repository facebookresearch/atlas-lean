# BWT from a prefix-free parse

Let $D$, $P$, $S$ and $f$ be the dictionary, parse, dictionary-suffix set and prefix map of a prefix-free parse of $T$ with window $w$, and $T' = T\dashv$. Let $g$ map each suffix $y$ of $T'$ to the unique suffix of $\#T\dashv^{w}$ beginning with $y$ (and $T'[n] = \dashv$ to $\#T\dashv^{w}$). Define $\beta$ to send the character $T'[i]$ ($i<n$) to the lexicographic rank in $S$ of $f(g(T'[i+1..n]))$, and $T'[n]$ to the rank of $f(T\dashv^{w})$.

**Lemma 6.** If $\beta$ maps exactly $k$ characters to $s \in S$, all of them copies of the same character $a$, and maps $t$ characters in total to elements of $S$ smaller than $s$, then positions $t+1, \dots, t+k$ of $\mathrm{BWT}(T')$ are copies of $a$.

**Lemma 7.** Let two suffixes of $\#T\dashv^{w}$ start with occurrences of the same $s \in S$, and let $q, q'$ be the suffixes of $P$ encoding the last $w$ characters of those occurrences of $s$ and the remainders. If the text suffixes compare as $t \prec t'$ then $q \prec q'$; so characters mapped to an ambiguous $s$ appear in the BWT in the order of the corresponding suffixes of $P$.

**Theorem.** $\mathrm{BWT}(T\dashv)$, the [Burrows–Wheeler transform](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/bwt.md) of $T$ with the sentinel $\dashv$, can be computed from $D$ and $P$ using workspace proportional to the total length of $P$ plus the elements of $D$, in $O(n)$ time when working in internal memory.

## Depends on

- [Burrows–Wheeler transform](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/bwt.md)
- [Prefix-free parse of a text](prefix-free-parse-of-a-text.md)

## Proof depends on

- [The transform from the suffix array](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/bwt-eq-map-suffix-array.md)

## Expansion

By Lemmas 4 and 5, $\beta$ is a partial sort of the characters of $T'$ consistent with their BWT order. Sorting the suffixes of the dictionary phrases fixes every block whose rank receives a single distinct preceding character (Lemma 6). Ranks receiving several distinct characters, which happen only when $s$ is a whole phrase or a suffix of several phrases, are resolved by suffix-sorting the parse $P$ over the alphabet of phrase ranks (Lemma 7). Both sorts run in linear time, but on inputs of size $|D| + |P|$ instead of $n$; on thousands of similar genomes $D$ and $P$ are orders of magnitude smaller than the text, which is what makes BWTs of whole pangenome collections feasible.

## Sources

- C. Boucher, T. Gagie, A. Kuhnle, B. Langmead, G. Manzini and T. Mun, "Prefix-free parsing for building big BWTs", Algorithms for Molecular Biology 14 (2019), 13, "Theory of prefix free parsing", Lemmas 6–7 and Theorem 1, <https://doi.org/10.1186/s13015-019-0148-5>, PMCID: PMC6534911.
