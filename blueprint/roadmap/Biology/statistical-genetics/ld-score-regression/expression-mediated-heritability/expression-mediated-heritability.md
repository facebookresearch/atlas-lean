# Expression-mediated heritability

Model a standardized trait for $N$ individuals as

$$y = X\gamma + XB\alpha + \epsilon,$$

where $X$ is an $N\times M$ standardized genotype matrix, $\gamma \in \mathbb R^M$ are non-mediated SNP effects (pleiotropic, linkage and trans-eQTL-mediated), $B = (\beta_{ji})$ is the $M\times G$ matrix of cis-eQTL effects in the causal cell types for $G$ genes, $\alpha \in \mathbb R^G$ are the causal effects of expression on the trait and $\epsilon$ is environmental noise. All effects are random. Assume the SNP columns of $X$ are uncorrelated (so that $h^2_{i,\mathrm{cis}} = \sum_j \beta_{ji}^2$ is the cis-heritability of gene $i$), and that the effects have zero cross moments and common second moments given the eQTL effects:

$$\mathbb E[\alpha_i\alpha_{i'} \mid B] = 0 \ (i \ne i'), \qquad \mathbb E[\alpha_i^2 \mid B] = \mathbb E[\alpha^2], \qquad \mathbb E[\gamma_j\gamma_{j'}] = 0 \ (j \ne j'), \qquad \mathbb E[\gamma_j^2] = \mathbb E[\gamma^2].$$

Exchangeability of the gene effects, independence of $\alpha$ from $B$, or zero covariance between squared gene and eQTL effects does not imply the first condition: with one SNP, two genes with $\beta_{11} = \beta_{12} = 1$ and $\alpha_1 = \alpha_2 = U$ for a centred random sign $U$ (suitably scaled), $\operatorname{Var}(XB\alpha) = 4\operatorname{Var}(U)$, while $G\,\mathbb E[\alpha^2]\,\mathbb E[h^2_{\mathrm{cis}}] = 2\operatorname{Var}(U)$.

**Definitions and decomposition.**

$$h^2_{\mathrm{med;causal}} = \operatorname{Var}(XB\alpha) = \mathbb E_{B,\alpha}\Big[\sum_{j=1}^M\Big(\sum_{i=1}^G\beta_{ji}\alpha_i\Big)^2\Big] = G\,\mathbb E[\alpha^2]\,\mathbb E[h^2_{\mathrm{cis}}],$$

$$h^2_{\mathrm{nonmed;causal}} = \operatorname{Var}(X\gamma) = M\,\mathbb E[\gamma^2],$$

where $\mathbb E[\alpha^2]$ is the average squared per-gene effect and $\mathbb E[h^2_{\mathrm{cis}}]$ the average cis-heritability of expression. For disjoint gene categories $D_d$, if instead of a single common second moment $\mathbb E[\alpha_i^2 \mid B] = \mathbb E[\alpha_i^2 \mid i \in D_d]$ is constant within each category (the cross moments still vanishing), then $h^2_{\mathrm{med;causal}}(D_d) = |D_d|\,\mathbb E[\alpha_i^2 \mid i \in D_d]\,\mathbb E[h^2_{i,\mathrm{cis}} \mid i \in D_d]$, where the last factor is the average cis-heritability over genes in $D_d$.

**Assayed tissues.** If expression is measured in tissues $\mathcal T$ rather than the causal contexts, the estimable quantity is $h^2_{\mathrm{med;assayed}}(\mathcal T) = r_g^2(\mathcal T)\,h^2_{\mathrm{med;causal}}$, where $r_g^2(\mathcal T)$ is the average squared genetic correlation of cis-expression between $\mathcal T$ and the causal contexts; the remainder $(1 - r_g^2(\mathcal T))\,h^2_{\mathrm{med;causal}}$ is counted as non-mediated.

## Remarks

By the law of total variance, $\operatorname{Var}(XB\alpha) = \mathbb E[\operatorname{Var}(XB\alpha \mid B,\alpha)] + \operatorname{Var}(\mathbb E[XB\alpha\mid B,\alpha])$, and the second term vanishes because the standardized genotypes have mean zero. Conditionally on $B,\alpha$, uncorrelated standardized SNPs give the variance $\sum_j\big(\sum_i\beta_{ji}\alpha_i\big)^2 = \sum_j\sum_{i,i'}\beta_{ji}\beta_{ji'}\alpha_i\alpha_{i'}$. Take the expectation over $\alpha$ given $B$ first: the zero cross moments remove the terms $i \ne i'$, and the common second moment gives $\mathbb E[\alpha^2]\sum_i\sum_j\beta_{ji}^2 = \mathbb E[\alpha^2]\sum_i h^2_{i,\mathrm{cis}}$; the expectation over $B$ then gives $G\,\mathbb E[\alpha^2]\,\mathbb E[h^2_{\mathrm{cis}}]$. Cross terms cannot be dropped before this expectation, since a realized $\alpha_i\alpha_{i'}$ need not vanish. The non-mediated term is the same computation for $\gamma$. Measuring expression in non-causal tissues attenuates the eQTL effects that can be correlated with the trait, which is why the assayed quantity is scaled by $r_g^2(\mathcal T)$.

## Sources

- D. W. Yao, L. J. O'Connor, A. L. Price et al., "Quantifying genetic effects on disease mediated by assayed gene expression levels", Nature Genetics (2020), Methods ("Definition of $h^2_{\mathrm{med}}$", "Unstratified MESC" with Equations 1–2 and the derivation of Equation 2, "Model assumptions", "Stratified MESC"), <https://doi.org/10.1038/s41588-020-0625-2> (PMC7276299).
