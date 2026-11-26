# Suffix array interval of a pattern

**Setting.** Let $T$ be a string of length $n$ over a totally ordered alphabet, terminated by a unique sentinel smaller than every letter. The suffix array $\mathrm{SA}$ is the permutation of $\{1, \dots, n\}$ with $T[\mathrm{SA}[1]..n] < T[\mathrm{SA}[2]..n] < \dots < T[\mathrm{SA}[n]..n]$ in lexicographic order.

**Proposition.** For every pattern $P$ of length $p$, the set of indices $k$ such that $P$ is a prefix of $T[\mathrm{SA}[k]..n]$ is a (possibly empty) contiguous interval $[\ell, u]$ of $\{1, \dots, n\}$. Hence the occurrences of $P$ in $T$ are exactly the positions $\mathrm{SA}[\ell], \dots, \mathrm{SA}[u]$, and $[\ell, u]$ can be found by two binary searches using $O(p \log n)$ character comparisons.

## Expansion

Suffixes having $P$ as a prefix are exactly those lying lexicographically between $P$ and $P$ followed by a symbol larger than every letter, and lexicographic order on the sorted suffixes is monotone, so they form an interval; each binary-search probe compares at most $p$ characters. A suffix array with its longest-common-prefix array (an enhanced suffix array) supports the same traversals as a suffix tree in linear space with smaller constants, which is why MUMmer4 replaced MUMmer3's suffix tree with a suffix array built by a fast suffix-sorting library.

## Sources

- G. Marçais, A. L. Delcher, A. M. Phillippy, R. Coston, S. L. Salzberg and A. Zimin, *MUMmer4: A fast and versatile genome alignment system*, PLoS Comput. Biol. 14 (2018), e1005944. <https://doi.org/10.1371/journal.pcbi.1005944> (PMCID: PMC5802927). Design and implementation.
- U. Manber and G. Myers, *Suffix arrays: a new method for on-line string searches*, SIAM J. Comput. 22 (1993), 935–948. <https://doi.org/10.1137/0222058>
- M. I. Abouelhoda, S. Kurtz and E. Ohlebusch, *Replacing suffix trees with enhanced suffix arrays*, J. Discrete Algorithms 2 (2004), 53–86. <https://doi.org/10.1016/S1570-8667(03)00065-0>
