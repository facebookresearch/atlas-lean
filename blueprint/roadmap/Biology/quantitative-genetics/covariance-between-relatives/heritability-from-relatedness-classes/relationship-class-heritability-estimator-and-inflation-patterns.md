# Relationship-class heritability estimator and its inflation patterns

For a class $R$ of relative pairs (full siblings, half-siblings, parent–offspring, grandparent–grandchild, avuncular, first cousins, ...), let $\rho_R$ be the phenotypic correlation over pairs in the class, $a_R$ the expected fraction of the genome shared identical by descent (the additive relationship: $1/2$ for full siblings and parent–offspring, $1/4$ for half-siblings, grandparent–grandchild and avuncular pairs, $1/8$ for first cousins), and $u_R$ the probability of sharing both alleles IBD ($1/4$ for full siblings, $0$ for the other classes listed). The class estimator is

$$\hat h^2_R = \frac{\rho_R}{a_R}.$$

Assume random mating and a phenotype with standardized variance components $h^2$ (additive), $d^2$ (dominance), $\varepsilon^2$ (additive-by-additive epistasis) and a class-specific shared-environment correlation $c_R$. Then

$$\mathbb E\,\hat h^2_R \approx h^2 + \frac{u_R}{a_R}\,d^2 + a_R\,\varepsilon^2 + \frac{c_R}{a_R},$$

so each source of inflation leaves a distinct signature across classes:

- **dominance** inflates only classes with $u_R > 0$, i.e. full siblings among these classes;
- **additive-by-additive epistasis** makes $\hat h^2_R$ increase monotonically with $a_R$, and gives equal estimates for classes with equal $a_R$ (half-siblings, grandparent–grandchild, avuncular);
- **shared environment** adds $c_R/a_R$, which differs between classes with the same $a_R$ and is amplified by $1/a_R$ (eightfold for first cousins).

In the Icelandic data, half-sibling estimates exceeded grandparent–grandchild estimates by $0.125$ on average despite equal $a_R$, and first cousins exceeded avuncular and grand-relative pairs, which points to shared environment rather than dominance or epistasis as the main source of inflation.

## Depends on

- [Full-sib covariance of genotypic values](../../fisher-s-decomposition-of-genetic-variance/cov-full-sibs.md)
- [Half-sib covariance of genotypic values](../../fisher-s-decomposition-of-genetic-variance/cov-half-sibs.md)

## Expansion

The covariance between relatives under the classical decomposition is $\operatorname{Cov} = a_R\sigma^2_A + u_R\sigma^2_D + a_R^2\sigma^2_{AA} + \dots$, plus any shared environmental covariance. Dividing by $a_R\sigma^2_P$ gives the displayed expectation (higher-order epistatic terms are dropped). Comparing classes with equal $a_R$ cancels both the additive and the additive-by-additive terms, so a difference between them can only come from dominance (absent when $u_R = 0$) or environment. No standard errors attach to individual class estimates because pairs overlap in complex pedigrees; differences are instead assessed across traits by a Wald test on the mean difference.

## Sources

- N. Zaitlen, P. Kraft, N. Patterson, B. Pasaniuc, G. Bhatia, S. Pollack, A. L. Price, "Using extended genealogy to estimate components of heritability for 23 quantitative and dichotomous traits", PLoS Genetics 9 (2013) e1003520, Results ("Estimation of heritability explained by shared environment, dominance, and epistasis") and Methods ("Heritability estimation of classes of related individuals"), <https://doi.org/10.1371/journal.pgen.1003520> (PMC3667752).
