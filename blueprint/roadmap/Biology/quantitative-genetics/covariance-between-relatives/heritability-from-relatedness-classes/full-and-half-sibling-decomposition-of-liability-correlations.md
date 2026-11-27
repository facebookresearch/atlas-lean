# Full- and maternal half-sibling decomposition of liability correlations

Let a binary diagnosis arise from a normally distributed liability with standardized variance components $A$ (additive genetic), $D$ (non-additive genetic), $C$ (shared environment) and $E$ (non-shared environment), $A + D + C + E = 1$. Let $r_{FS}$ and $r_{HS}$ be the tetrachoric (liability-scale) correlations of the diagnosis in full-sibling pairs and in maternal half-sibling pairs. Assume:

1. full siblings share on average $1/2$ of additive and $1/4$ of non-additive genetic effects;
2. maternal half-siblings share $1/4$ of additive and $0$ of non-additive genetic effects;
3. shared environment is fully shared within both kinds of pair;
4. non-shared environment is unique to each individual.

Then

$$r_{FS} = \tfrac12 A + \tfrac14 D + C, \qquad r_{HS} = \tfrac14 A + C .$$

These two equations cannot identify all three of $A, C, D$. Under the ACE submodel ($D = 0$) they solve uniquely:

$$A = 4\,(r_{FS} - r_{HS}), \qquad C = 2\,r_{HS} - r_{FS}, \qquad E = 1 - A - C,$$

and under the ADE submodel ($C = 0$), $A = 4 r_{HS}$ and $D = 4 r_{FS} - 8 r_{HS}$. Two heritability estimates $\hat h_1^2, \hat h_2^2$ from independent designs are compared with $Z = (\hat h_1^2 - \hat h_2^2)/\sqrt{\mathrm{se}_1^2 + \mathrm{se}_2^2}$ against a standard normal.

## Depends on

- [Full-sib covariance of genotypic values](../../fisher-s-decomposition-of-genetic-variance/cov-full-sibs.md)
- [Half-sib covariance of genotypic values](../../fisher-s-decomposition-of-genetic-variance/cov-half-sibs.md)

## Expansion

The coefficients are the expected additive and dominance sharing: full siblings are IBD at one allele with probability $1/2$ and at both with probability $1/4$, giving $\tfrac12\sigma^2_A + \tfrac14\sigma^2_D$; maternal half-siblings share one parent, hence $\tfrac14\sigma^2_A$ and no dominance covariance. Subtracting the two equations eliminates $C$ under ACE: $r_{FS} - r_{HS} = A/4$. The design trades the twin study's MZ/DZ contrast for a much larger register-based sample, but it relies on equal environmental sharing in full and half-sibling pairs, which age gaps and split households can violate, and on random mating. In Swedish register data on about 4.4 million siblings, shared-environment estimates for eight psychiatric disorders were non-significant and family-based heritabilities exceeded SNP heritabilities for most disorders.

## Sources

- E. Pettersson, P. Lichtenstein, H. Larsson, J. Song, et al., "Genetic influences on eight psychiatric disorders based on family data of 4 408 646 full and half-siblings, and genetic data of 333 748 cases and controls", Psychological Medicine 49 (2019), Methods ("Family data (h2-national)", "Statistical analyses") and Table 1, <https://doi.org/10.1017/s0033291718002039> (PMC6421104).
