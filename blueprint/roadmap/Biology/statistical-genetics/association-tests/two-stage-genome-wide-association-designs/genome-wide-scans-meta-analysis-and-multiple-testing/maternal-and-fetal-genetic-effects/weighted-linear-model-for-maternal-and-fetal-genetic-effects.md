# Weighted linear model for maternal and fetal genetic effects

Let a perinatal trait (birth weight) of an individual satisfy, at one biallelic SNP,

$$Y = \beta_f\, G_{\mathrm{own}} + \beta_m\, G_{\mathrm{mother}} + e,$$

where $G_{\mathrm{own}}$ and $G_{\mathrm{mother}}$ are the allele counts of the individual and of their mother, $\beta_f$ is the fetal (direct) effect, $\beta_m$ the maternal (intrauterine) effect, and $e$ is uncorrelated with both genotypes. Assume random mating and Hardy–Weinberg proportions, so $\operatorname{Var}(G_{\mathrm{own}}) = \operatorname{Var}(G_{\mathrm{mother}})$ and $\operatorname{Cov}(G_{\mathrm{own}}, G_{\mathrm{mother}}) = \tfrac12\operatorname{Var}(G)$. Two marginal GWAS are run: own trait on own genotype (slope $\beta_f^{\mathrm{unadj}}$), and offspring's trait on the parent's (mother's) genotype (slope $\beta_m^{\mathrm{unadj}}$).

**Proposition.** The population slopes are

$$\beta_f^{\mathrm{unadj}} = \beta_f + \tfrac12\beta_m, \qquad \beta_m^{\mathrm{unadj}} = \beta_m + \tfrac12\beta_f,$$

so the adjusted effects are recovered by the linear transformation

$$\hat\beta_f^{\mathrm{adj}} = \tfrac43\,\hat\beta_f^{\mathrm{unadj}} - \tfrac23\,\hat\beta_m^{\mathrm{unadj}}, \qquad \hat\beta_m^{\mathrm{adj}} = \tfrac43\,\hat\beta_m^{\mathrm{unadj}} - \tfrac23\,\hat\beta_f^{\mathrm{unadj}} .$$

If the two GWAS use independent samples, $\operatorname{Var}(\hat\beta_f^{\mathrm{adj}}) = \tfrac{16}{9}\operatorname{Var}(\hat\beta_f^{\mathrm{unadj}}) + \tfrac49\operatorname{Var}(\hat\beta_m^{\mathrm{unadj}})$, and symmetrically for $\hat\beta_m^{\mathrm{adj}}$; overlapping samples add a covariance term.

## Proof sketch

The least-squares slope of $Y$ on $G_{\mathrm{own}}$ is $\operatorname{Cov}(Y, G_{\mathrm{own}})/\operatorname{Var}(G_{\mathrm{own}}) = \beta_f + \beta_m\operatorname{Cov}(G_{\mathrm{mother}}, G_{\mathrm{own}})/\operatorname{Var}(G) = \beta_f + \beta_m/2$, because a child inherits one of the mother's two alleles. Applying the same model to the offspring of a mother gives $\beta_m + \beta_f/2$. The $2 \times 2$ system has determinant $3/4$, whose inverse gives the coefficients $4/3$ and $-2/3$. Warrington et al. call this the weighted linear model (WLM) and use it as a genome-wide approximation to a structural equation model fitted jointly to individuals with own, offspring, or both birth weights; the WLM reproduced the structural-equation estimates at the lead SNPs and lowered the genetic correlation between maternal and fetal effects from $0.82$ (unadjusted) to $0.10$. Paternal genotype enters only through the child's genotype and needs no separate term under random mating.

## Depends on

- [Hardy–Weinberg proportions](../../../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Sources

- N. M. Warrington, R. N. Beaumont, M. Horikoshi et al., "Maternal and fetal genetic effects on birth weight and their relevance to cardio-metabolic risk factors", Nature Genetics 51 (2019), 804–814, Results and Methods section "Approximation of the SEM for genome-wide analyses", <https://doi.org/10.1038/s41588-019-0403-1> (PMCID: PMC6522365).
