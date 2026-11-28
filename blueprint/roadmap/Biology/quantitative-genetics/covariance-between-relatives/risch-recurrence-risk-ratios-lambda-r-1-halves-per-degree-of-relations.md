# Risch's recurrence-risk ratios for relatives

For a binary disease with population prevalence $K$, the recurrence risk $K_R$ for relatives of type $R$ is the probability that the relative is affected given that the proband is, and $\lambda_R = K_R/K$. Risch (1990) shows that for a single-locus model $\lambda_R - 1$ decreases by a factor of two with each degree of unilineal relationship, that is, along relationships with $\Delta_R = 0$ (parents and offspring, then unilineal second- and higher-degree relatives), or along every relationship when the dominance variance $V_D$ is $0$; siblings, with $\Delta_R = 1/4 > 0$, carry an extra dominance term, and bilineal relatives such as double first cousins, which also have $\Delta_R > 0$, differ in the same way. The same holds for an additive multilocus model. The multiplicative (epistatic) multilocus model, in which $\lambda_R$ is the product of the locus ratios and $\lambda_R - 1$ decreases more rapidly, is [stated separately](../../statistical-genetics/risch-recurrence-risk-ratios-for-multilocus-trai/prod-sub-one-ge-two-mul.md).

The single-locus statement follows from the [single-locus covariance between relatives in Cockerham form](../../../Biology/quantitative-genetics/covariance-between-relatives/rel-cov-eq-cov.md), $\mathrm{Cov} = \sum_{i,j} (2\phi_R)^i \Delta_R^j V_{ij}$, which for one locus has only the additive term $V_{10} = V_A$ and the dominance term $V_{01} = V_D$: if affection is determined by penetrances at one locus in a randomly mating population, the covariance of the two affection indicators is $2\phi_R V_A + \Delta_R V_D$, with $V_A$ and $V_D$ the additive and dominance variances of the penetrance, $\phi_R$ the kinship coefficient of the relatives and $\Delta_R$ the probability that they share both genes identical by descent. Since $K_R = (K^2 + \mathrm{Cov})/K$,

$$\lambda_R - 1 = \frac{2\phi_R V_A + \Delta_R V_D}{K^2}.$$

For relatives with $\Delta_R = 0$ (parents and offspring, and unilineal second- and higher-degree relatives), or when $V_D = 0$, $\lambda_R - 1$ is proportional to $\phi_R$, which halves with each degree of unilineal relationship.

## Depends on

- [Prevalence](../../statistical-genetics/risch-recurrence-risk-ratios-for-multilocus-trai/prevalence.md)
- [Risch's recurrence-risk ratio](../../statistical-genetics/risch-recurrence-risk-ratios-for-multilocus-trai/recurrence-ratio.md)
- [Single-locus covariance between relatives in Cockerham form](../../../Biology/quantitative-genetics/covariance-between-relatives/rel-cov-eq-cov.md)
- [Malécot's recursion computes gene-dropping kinship](../../../Biology/quantitative-genetics/pedigree-kinship-and-inbreeding/gene-drop-kinship-eq-kinship.md)

## Expansion

1. The model: one locus, penetrance as a function of the genotype, random mating, and relatives described by their identity-by-descent probabilities.
2. The specialization of the Cockerham-form covariance to affection indicators, with the penetrance as genotypic value.
3. The identity for $\lambda_R - 1$ and the halving per degree when $\Delta_R = 0$ or $V_D = 0$.
4. The additive multilocus model of the source.
5. The role of $\lambda_R$ in the power of affected-relative-pair linkage tests, as a separate statement.

## Sources

- N. Risch, Linkage strategies for genetically complex traits. I. Multilocus models, Am. J. Hum. Genet. 46 (1990), 222–228, abstract.
