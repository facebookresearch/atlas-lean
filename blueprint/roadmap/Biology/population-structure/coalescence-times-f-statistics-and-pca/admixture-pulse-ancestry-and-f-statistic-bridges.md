# Admixture pulses, coalescence times and f-statistics

Peter (2016) expresses the $F$-statistics through expected pairwise coalescence times: $F_2(P_1, P_2) = \theta\bigl(E T_{12} - \frac12(E T_{11} + E T_{22})\bigr)$ (his Equation 16), $F_3(P_X; P_1, P_2) = \frac{\theta}{2}(E T_{1X} + E T_{2X} - E T_{12} - E T_{XX})$ (Equation 20c) and $F_4(P_1, P_2; P_3, P_4) = \frac{\theta}{2}(E T_{14} + E T_{23} - E T_{13} - E T_{24})$ (Equation 24c). In the simplest pulse model, an ancestral population splits into $P_1$ and $P_2$ at time $t_r$ in the past, and at time $t_1 < t_r$ the population $P_X$ is formed so that each of its individuals descends from $P_1$ with probability $\alpha$ and from $P_2$ with probability $1 - \alpha$; backward in time, each lineage of $P_X$ that has not coalesced by $t_1$ moves to $P_1$ or $P_2$ independently with these probabilities. Evaluating the expected coalescence times in this model under the assumption, made in his appendix derivation (Equations 33–34), that all populations have the same size $1$, Peter finds that $F_3(P_X; P_1, P_2) < 0$ exactly when

$$\frac{1}{1 - c_x}\,\frac{t_1}{t_r} < 2\alpha(1 - \alpha)$$

(Equation 22), where $c_x$ is the probability that two lineages sampled in $P_X$ coalesce before $t_1$, which he gives as $1 - \exp(-\int_0^{t_1} N(s)^{-1}\,ds)$ for a randomly mating population of changing size $N(t)$, a case the equal-size derivation does not itself cover; so the test has most power when $\alpha$ is near $1/2$, when the admixture is recent relative to the split, and when $P_X$ is large. In his appendix the same bookkeeping, with the same equal-size assumption, gives an $F_4$ statistic for an admixed population proportional to the admixture fraction times a difference of split times. Among the models he examined, a hierarchical stepping-stone model, with demes grouped into populations, is the only one besides admixture graphs in which $F_3$ can be negative, so a negative $F_3$ does not by itself distinguish admixture from population structure.

## Depends on

- [$f_2$ in terms of expected coalescence times](../../../Biology/population-structure/coalescence-times-f-statistics-and-pca/f2-eq.md)
- [$f_3$ in terms of expected coalescence times](../../../Biology/population-structure/coalescence-times-f-statistics-and-pca/f3-eq.md)
- [$f_4$ in terms of expected coalescence times](../../../Biology/population-structure/coalescence-times-f-statistics-and-pca/f4-eq.md)

## Expansion

1. The pulse model with split time $t_r$, admixture time $t_1$ and proportion $\alpha$, and the independent assignment of unmerged lineages at the pulse.
2. The expected pairwise coalescence times $E T_{1X}$, $E T_{2X}$, $E T_{XX}$ and $E T_{12}$ in the pulse model, with the coalescence probability $c_x$ before the pulse.
3. The negativity condition (Equation 22) for $F_3$ and its dependence on $\alpha$, $t_1/t_r$ and $c_x$.
4. The $F_4$ statistic of the admixed population in the pulse model, as computed in the appendix.
5. Structured models in which $F_3$ is negative without admixture (hierarchical stepping-stone), as counterexamples.

## Sources

- B. M. Peter, Admixture, population structure, and F-statistics, Genetics 202 (2016), 1485–1501, Equations 16, 20c, 22 and 24c, and Appendix. <https://doi.org/10.1534/genetics.115.183913>
