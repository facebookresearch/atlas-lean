# RDR variance decomposition and covariance model

Let $Y$ be a quantitative phenotype in a population whose members have both parents genotyped. Assume direct genetic effects are additive and there is no gene-by-environment interaction. Call the effect of an individual's own genome on its own phenotype **direct**, and the effect of relatives' genomes (for example parental genetic nurture) **indirect**; indirect effects are part of the environment of the proband.

**Variance decomposition.** Write $Y = D + E + \epsilon$, with $D$ the direct genetic component and $E$ the environmental component correlated with parental genotype (including parental genetic nurture). Then

$$\operatorname{Var}(Y) = v_g + v_{e\sim g} + c_{g,e} + \operatorname{Var}(\epsilon),$$

where $v_g = \operatorname{Var}(D)$ is the variance explained by direct genetic effects and $h^2 = v_g / \operatorname{Var}(Y)$ is the (direct) heritability, $v_{e\sim g} = \operatorname{Var}(E)$, $c_{g,e} = 2\operatorname{Cov}(D, E)$ is twice the covariance between the direct genetic component and the environmental component correlated with parental genotype, and $\epsilon$ is uncorrelated with both proband and parental genotypes.

Young et al. call $c_{g,e}$ the covariance between direct genetic and environmental effects; this page defines it as twice that covariance. The source standardises $G$ to variance one and $G_{par}$ to "mean zero and variance two", and builds $R_{o,par}^{snp} = (2l)^{-1}(G G_{par}^T + G_{par} G^T)$, "calculated in this way to ensure estimates of vg, ve~g, and cg,e are properly calibrated". Then $[R_{o,\mathrm{par}}]_{ii} \approx 1$, and since $\operatorname{Var}(D + E + \epsilon) = \operatorname{Var} D + \operatorname{Var} E + 2\operatorname{Cov}(D, E) + \operatorname{Var}\epsilon$, the diagonal of the covariance model below reproduces the decomposition only when $c_{g,e} = 2\operatorname{Cov}(D, E)$.

**RDR covariance model.** For a vector $\mathbf Y$ of phenotypes,

$$\operatorname{Cov}(\mathbf Y) = v_g R + v_{e\sim g} R_{\mathrm{par}} + c_{g,e} R_{o,\mathrm{par}} + \operatorname{Cov}(\epsilon),$$

where $[R]_{ij}$ is the realized (identity-by-descent) relatedness of $i$ and $j$, $[R_{\mathrm{par}}]_{ij}$ the relatedness of the parents of $i$ with the parents of $j$, and $[R_{o,\mathrm{par}}]_{ij}$ the relatedness of each of $i, j$ with the parents of the other. RDR fits this model with the working assumption $\operatorname{Cov}(\epsilon) = \sigma^2 I$.

**Relatedness disequilibrium.** For pairs in which neither is a direct ancestor of the other,

$$\mathbb E\bigl([R]_{ij} \mid [R_{\mathrm{par}}]_{ij}\bigr) = \tfrac12 [R_{\mathrm{par}}]_{ij},$$

and the deviation $[R]_{ij} - \tfrac12 [R_{\mathrm{par}}]_{ij}$, the relatedness disequilibrium, is produced by random segregation in the parents. Because it is independent of shared environment apart from indirect genetic effects between the pair, the RDR estimate of $h^2$ converges to the true direct heritability when the sample excludes pairs with indirect genetic effects on each other and ancestor-descendant pairs, even if $\operatorname{Cov}(\epsilon) \ne \sigma^2 I$.

## Depends on

- [GREML covariance matrix](../../greml-and-haseman-elston-estimation-of-snp-herit/greml-cov.md)

## Expansion

The construction parallels the transmission disequilibrium test: offspring genotype equals half the parental genotype sum plus segregation noise, and the TDT conditions on parental genotype; RDR conditions on parental relatedness instead. Fitting $R$ jointly with $R_{\mathrm{par}}$ means $v_g$ is identified only from the segregation-driven deviation of $R$ around $R_{\mathrm{par}}/2$, which family environment, regional stratification and parental nurture cannot mimic. The model reduces to GREML (with $R$ in place of the SNP relationship matrix) when the parental terms are dropped. Replacing all three matrices by SNP-based estimates gives RDR-SNP. In an Icelandic sample of 54,888 probands with both parents genotyped, RDR gave height $h^2 = 55.4\%$ (s.e. $4.4\%$) and educational attainment $17.0\%$ (s.e. $9.4\%$).

## Sources

- A. I. Young, M. L. Frigge, D. F. Gudbjartsson, et al., "Relatedness disequilibrium regression estimates heritability without environmental bias", *Nature Genetics* (2018), <https://doi.org/10.1038/s41588-018-0178-9> (PMC6130754; Equations (1) and (2), section "Environmental bias properties of RDR"; the convergence proof is in the Supplementary Note).
