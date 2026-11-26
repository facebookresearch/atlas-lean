# Within-sibship genotype decomposition and direct genetic effects

Let sibship $i$ contain $n_i \ge 2$ full siblings with genotypes $G_{ij} \in \{0, 1, 2\}$ at an autosomal variant, $j = 1, \dots, n_i$, and phenotypes $X_{ij}$. Decompose each genotype into the **sibship mean** and the **within-sibship deviation**

$$G^F_i = \frac{1}{n_i} \sum_{j=1}^{n_i} G_{ij}, \qquad G^C_{ij} = G_{ij} - G^F_i .$$

The **population model** regresses $X_{ij}$ on $G_{ij}$ and covariates (age, sex, principal components); the **within-sibship model** regresses $X_{ij}$ on $G^C_{ij}$ and $G^F_i$ jointly with the same covariates, and its coefficient $\beta_W$ on $G^C_{ij}$ is the within-sibship estimate.

**Properties.**

1. $\sum_{j} G^C_{ij} = 0$ in every sibship, so $G^C$ is orthogonal to every variable that is constant within sibships. By the Frisch–Waugh–Lovell theorem, without further covariates the least-squares estimate is the fixed-effects (sibling-difference) estimator

$$\hat\beta_W = \frac{\sum_{i,j} G^C_{ij} X_{ij}}{\sum_{i,j} (G^C_{ij})^2}.$$

2. Under Mendelian segregation every sibling has $\mathbb E[G_{ij} \mid G_{P,i}, G_{M,i}] = (G_{P,i} + G_{M,i})/2$, so $\mathbb E[G^C_{ij} \mid G_{P,i}, G_{M,i}] = 0$: the deviation reflects only the randomness of meiosis and is uncorrelated with any function of the parental genotypes and with family-level confounders.
3. Consequently $\beta_W$ is free of bias from population stratification, assortative mating and indirect genetic effects of parents, which load on $G^F_i$; it can still absorb indirect genetic effects of the siblings themselves.

## Expansion

Conditionally on the parents, each transmitted allele is a fair coin flip independent across siblings, so differences among siblings are a randomized experiment on genotype. Family-level sources of association (ancestry, assortment, parental nurture) shift all siblings of a family together and are absorbed by $G^F_i$. Standard errors are clustered by sibship; in the population model, unmodeled relatedness between sibships additionally deflates standard errors, whereas the within-sibship standard errors are unaffected (Methods). Meta-analyzed across 178,076 siblings, within-sibship estimates were markedly smaller than population estimates for traits such as height and educational attainment.

## Sources

- L. J. Howe, M. G. Nivard, T. T. Morris, et al., *Within-sibship genome-wide association analyses decrease bias in estimates of direct genetic effects*, Nat. Genet. (2022). <https://doi.org/10.1038/s41588-022-01062-7> (PMCID: PMC9110300)
