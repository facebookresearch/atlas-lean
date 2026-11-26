# LF mapping of the Burrows–Wheeler transform

Let $T[0..n-1]$ be a string over an ordered alphabet ending with a unique smallest terminator, and let $\mathrm{SA}$ be its suffix array (starting positions of suffixes in lexicographic order). The **Burrows–Wheeler transform** is the string $\mathrm{BWT}[i] = T[\mathrm{SA}[i] - 1]$ (taken cyclically), the character preceding each suffix in sorted order. Let $C[c]$ be the number of characters of $T$ strictly smaller than $c$, and $\mathrm{rank}_c(i)$ the number of occurrences of $c$ in $\mathrm{BWT}[0..i]$.

**LF mapping.** The position in sorted order of the suffix that starts one character earlier than suffix $\mathrm{SA}[i]$ is
$$\mathrm{LF}(i) = C\big[\mathrm{BWT}[i]\big] + \mathrm{rank}_{\mathrm{BWT}[i]}(i)$$
(with the indexing convention fixing an additive constant). LF is the inverse of the successor map $\Psi$, and for each character $c$ it maps the BWT positions holding $c$, in order, to a contiguous increasing run of suffix-array positions.

**Backward search.** If $[b, e]$ is the suffix-array interval of suffixes beginning with $P[i..m-1]$, then the interval for $P[i-1..m-1]$ is
$$\big[\,C[c] + \mathrm{rank}_c(b-1) + 1,\ C[c] + \mathrm{rank}_c(e)\,\big], \qquad c = P[i-1],$$
so pattern counting takes $m$ pairs of rank queries on the BWT. This is the basis of the FM-index.

## Expansion

Suffixes preceded by the same character $c$ keep their relative order after $c$ is prepended, because prepending a common first character does not change lexicographic comparisons of the remainders. Hence the $j$-th occurrence of $c$ in the BWT corresponds to the $j$-th suffix starting with $c$, which sits at position $C[c] + j$; this is the LF formula. Backward search applies the same observation to the endpoints of an interval.

## Sources

- C. Boucher, T. Gagie, A. Kuhnle, B. Langmead, G. Manzini and T. Mun, "Prefix-free parsing for building big BWTs", Algorithms for Molecular Biology 14 (2019), 13, Background (suffix arrays, LF mapping and FM-indexes), <https://doi.org/10.1186/s13015-019-0148-5>, PMCID: PMC6534911.
- P. Ferragina and G. Manzini, "Opportunistic data structures with applications", Proceedings of the 41st IEEE Symposium on Foundations of Computer Science (2000), 390–398, <https://doi.org/10.1109/SFCS.2000.892127>.
