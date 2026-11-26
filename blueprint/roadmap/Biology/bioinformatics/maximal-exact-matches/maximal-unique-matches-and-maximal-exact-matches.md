# Maximal unique matches and maximal exact matches

**Setting.** Let $R$ (reference, length $n$) and $Q$ (query, length $m$) be strings and $L \ge 1$ a minimum length. An *exact match* is a triple $(i, j, \lambda)$ with $\lambda \ge 1$ and $R[i..i+\lambda-1] = Q[j..j+\lambda-1]$.

**Definitions.**

- The match is *maximal* if it cannot be extended: ($i = 1$ or $j = 1$ or $R[i-1] \ne Q[j-1]$) and ($i + \lambda - 1 = n$ or $j + \lambda - 1 = m$ or $R[i+\lambda] \ne Q[j+\lambda]$).
- A *maximal exact match* (MEM) is a maximal exact match with $\lambda \ge L$.
- A *maximal unique match* (MUM) is a MEM whose string $R[i..i+\lambda-1]$ occurs exactly once in $R$ (the default in MUMmer); the stricter variant also requires exactly one occurrence in $Q$.

**Proposition.** Distinct MUMs (in either variant) start at distinct query positions $j$. Hence there are at most $m$ MUMs, whereas the number of MEMs can grow quadratically in repetitive inputs.

**Algorithmic fact.** All MEMs or MUMs of length at least $L$ can be enumerated in $O(n + m + z)$ time, where $z$ is the output size, from a suffix tree or an enhanced suffix array of $R$.

## Depends on

- [Suffix array interval of a pattern](suffix-array-interval-of-a-pattern.md)

## Expansion

Suppose two MUMs $(i, j, \lambda)$ and $(i', j, \lambda')$ share $j$ with $\lambda \le \lambda'$. Then $Q[j..j+\lambda-1]$ is a prefix of $R[i'..i'+\lambda'-1]$, so it occurs at $i'$; uniqueness in $R$ forces $i = i'$. If $\lambda < \lambda'$ then $R[i+\lambda] = Q[j+\lambda]$, contradicting right-maximality, so the two MUMs coincide. For MEMs, the strings $\mathtt{a}^n$ and $\mathtt{a}^m$ already give $\Theta(nm)$ maximal matches, which is why the source warns that the MEM option can produce very large output on repeats. In the NUCmer pipeline the matches are clustered by proximity and the gaps between consecutive matches are filled by banded Smith–Waterman alignment.

## Sources

- G. Marçais, A. L. Delcher, A. M. Phillippy, R. Coston, S. L. Salzberg and A. Zimin, *MUMmer4: A fast and versatile genome alignment system*, PLoS Comput. Biol. 14 (2018), e1005944. <https://doi.org/10.1371/journal.pcbi.1005944> (PMCID: PMC5802927). Design and implementation.
- A. L. Delcher, S. Kasif, R. D. Fleischmann, J. Peterson, O. White and S. L. Salzberg, *Alignment of whole genomes*, Nucleic Acids Res. 27 (1999), 2369–2376. <https://doi.org/10.1093/nar/27.11.2369>
- M. I. Abouelhoda, S. Kurtz and E. Ohlebusch, *Replacing suffix trees with enhanced suffix arrays*, J. Discrete Algorithms 2 (2004), 53–86. <https://doi.org/10.1016/S1570-8667(03)00065-0>
