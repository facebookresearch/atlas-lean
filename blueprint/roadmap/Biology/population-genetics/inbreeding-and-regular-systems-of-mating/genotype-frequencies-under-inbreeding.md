# Genotype frequencies of an inbred individual

Let a base population be in Hardy–Weinberg proportions at a locus with alleles $A_1, \dots, A_k$ of
frequencies $p_1, \dots, p_k$ ($p_i \ge 0$, $\sum_i p_i = 1$). Consider an individual whose inbreeding
coefficient relative to this base population is $F \in [0, 1]$ (in a pedigree, the
[inbreeding coefficient](../../quantitative-genetics/pedigree-kinship-and-inbreeding/inbreeding.md) of an
individual): with probability $F$ the two gene copies descend from the same base-population copy
and carry one shared allele drawn with frequencies $p$. With probability $1 - F$ they descend from two
distinct copies and carry independent alleles drawn with frequencies $p$. Assume no mutation since the
base population and no selection. Then the individual has genotype

- $A_iA_i$ with probability $F p_i + (1 - F) p_i^2$, and
- $A_iA_j$ ($i \ne j$, unordered) with probability $2 (1 - F) p_i p_j$.

If two distinct alleles $A_1$ and $A_2$ exhaust the base frequency mass (all other alleles, if any,
have frequency zero), set $p = p_1$ and $q = 1 - p$. Then the frequencies of $A_1A_1$, $A_1A_2$
and $A_2A_2$ are $p^2 + Fpq$, $2pq(1 - F)$ and $q^2 + Fpq$. The genotype probabilities sum to $1$,
and a uniformly chosen gene copy from the individual has allele $A_i$ with probability $p_i$ for every
$F$. The total heterozygote probability is $(1 - F)$ times its Hardy–Weinberg value $1 - \sum_i p_i^2$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section V.2 "Inbreeding Coefficients and Genotype Frequencies", equations (V-2)–(V-3), pp. 219–220; Section V.14, equations (V-46)–(V-47), p. 243.
