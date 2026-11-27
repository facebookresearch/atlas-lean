# Genotype frequencies of an inbred individual

Let a base population be in Hardy–Weinberg proportions at a locus with alleles $A_1, \dots, A_k$ of
frequencies $p_1, \dots, p_k$ ($p_i \ge 0$, $\sum_i p_i = 1$). Consider an individual whose inbreeding
coefficient relative to this base population is $F \in [0, 1]$ (in a pedigree, the
[inbreeding coefficient](../../quantitative-genetics/pedigree-kinship-and-inbreeding/inbreeding.md) of an
individual): with probability $F$ its two gene
copies are identical by descent, that is, copies of one gene of the base population, and with
probability $1 - F$ they are copies of two distinct genes of the base population, which then carry
independent alleles drawn with the frequencies $p$. Assume no mutation since the base population and no
selection. Then the individual has genotype

- $A_iA_i$ with probability $F p_i + (1 - F) p_i^2$, and
- $A_iA_j$ ($i \ne j$, unordered) with probability $2 (1 - F) p_i p_j$.

In the biallelic case, with $p = p_1$ and $q = 1 - p$, the genotype frequencies of $A_1A_1$, $A_1A_2$
and $A_2A_2$ are $p^2 + Fpq$, $2pq(1 - F)$ and $q^2 + Fpq$. The probabilities sum to $1$, the
frequency of $A_i$ among the individual's genes is $p_i$ for every $F$, and the heterozygote frequency
is $(1 - F)$ times its Hardy–Weinberg value $1 - \sum_i p_i^2$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section V.2 "Inbreeding Coefficients and Genotype Frequencies", equation (V-2), p. 219
  (biallelic case and the model's assumptions); Section V.14, equations (V-46)–(V-47), p. 243. The
  multiallelic formulas follow from the same two-case total-probability argument and are not stated in
  the source.
