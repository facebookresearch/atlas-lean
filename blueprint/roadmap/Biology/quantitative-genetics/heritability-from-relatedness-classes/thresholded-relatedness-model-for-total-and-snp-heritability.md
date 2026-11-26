# Thresholded-relatedness variance-component model for total and SNP heritability

Let $Y \in \mathbb R^n$ be a standardized phenotype (mean $0$, variance $1$ after fixed effects $X\beta$) for $n$ genotyped individuals, possibly including close relatives. From $N$ genotyped SNPs with genotypes $x_{ij} \in \{0,1,2\}$ and allele frequencies $p_i$, form the identity-by-state genetic relationship matrix

$$K^{\mathrm{IBS}}_{jk} = \frac1N\sum_{i=1}^{N}\frac{(x_{ij}-2p_i)(x_{ik}-2p_i)}{2p_i(1-p_i)},$$

and its thresholded version $K^{\mathrm{IBS}>t}$, obtained by setting every off-diagonal entry $\le t$ to $0$ and leaving the diagonal unchanged. The joint model is

$$Y \sim \mathcal N\!\Bigl(X\beta,\ \ h^2_{t+}\,K^{\mathrm{IBS}>t} + h^2_{g+}\,K^{\mathrm{IBS}} + \bigl(1 - h^2_{t+} - h^2_{g+}\bigr) I_n\Bigr),$$

fitted by restricted maximum likelihood. Its two estimates are

- $\hat h^2_{g} = \hat h^2_{g+}$, the heritability explained by genotyped SNPs (and variants in linkage disequilibrium with them);
- $\hat h^2 = \hat h^2_{t+} + \hat h^2_{g+}$, the total narrow-sense heritability.

Relatives therefore need not be removed before estimating SNP heritability, and both quantities come from the same sample. Replacing $K^{\mathrm{IBS}>t}$ by an identity-by-descent matrix $K^{\mathrm{IBD}}$ (fraction of genome shared IBD, from long-range phased data) gives the same decomposition. Thresholds $t \in \{0, 0.025, 0.05\}$ were examined; a single-component fit on $K^{\mathrm{IBS}>t}$ was biased downward at $t = 0$.

A related two-component model with $K^{\mathrm{IBD}}$ and $K^{\mathrm{IBD2}}$ (the fraction of genome shared IBD on both homologues) gives a narrow-sense heritability and a component that combines dominance, shared environment and epistasis; a one-degree-of-freedom likelihood ratio test against the $K^{\mathrm{IBD}}$-only model tests that combined component.

## Depends on

- [Genetic relationship matrix](../../statistical-genetics/greml-and-haseman-elston-estimation-of-snp-herit/grm.md)
- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](../../statistical-genetics/greml-and-haseman-elston-estimation-of-snp-herit/greml-cov.md)

## Expansion

Large entries of $K^{\mathrm{IBS}}$ belong to close relatives, and for them genome-wide IBS sharing is a good estimate of IBD sharing, which tags every causal variant, rare ones included. Small entries belong to distant pairs, among whom genotype similarity carries information only about causal variants tagged by the array. A single $K^{\mathrm{IBS}}$ applied to a sample with relatives therefore mixes the two regimes and estimates neither quantity. Splitting it lets the thresholded matrix absorb the additional phenotypic covariance of close relatives (the untagged part of $h^2$), while the full matrix, dominated by distant pairs, measures $h^2_g$.

## Sources

- N. Zaitlen, P. Kraft, N. Patterson, B. Pasaniuc, G. Bhatia, S. Pollack, A. L. Price, "Using extended genealogy to estimate components of heritability for 23 quantitative and dichotomous traits", PLoS Genetics 9 (2013) e1003520, Methods ("Statistical methods", Equations (1)–(2)) and Results, <https://doi.org/10.1371/journal.pgen.1003520> (PMC3667752).
