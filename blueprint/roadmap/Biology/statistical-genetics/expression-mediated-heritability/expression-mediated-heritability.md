# Expression-mediated heritability

Model a standardized trait for $N$ individuals as

$$y = X\gamma + XB\alpha + \epsilon,$$

where $X$ is an $N\times M$ standardized genotype matrix, $\gamma \in \mathbb R^M$ are non-mediated SNP effects (pleiotropic, linkage and trans-eQTL-mediated), $B = (\beta_{ji})$ is the $M\times G$ matrix of cis-eQTL effects in the causal cell types for $G$ genes, $\alpha \in \mathbb R^G$ are the causal effects of expression on the trait and $\epsilon$ is environmental noise. All effects are random, with $\alpha$ independent of $B$ and the gene effects exchangeable across genes.

**Definitions and decomposition.**

$$h^2_{\mathrm{med;causal}} = \operatorname{Var}(XB\alpha) = \mathbb E_{B,\alpha}\Big[\sum_{i=1}^G\sum_{j=1}^M\beta_{ji}^2\alpha_i^2\Big] = G\,\mathbb E[\alpha^2]\,\mathbb E[h^2_{\mathrm{cis}}],$$

$$h^2_{\mathrm{nonmed;causal}} = \operatorname{Var}(X\gamma) = M\,\mathbb E[\gamma^2],$$

where $\mathbb E[\alpha^2]$ is the average squared per-gene effect and $\mathbb E[h^2_{\mathrm{cis}}]$ the average cis-heritability of expression. For gene categories $D_d$, $h^2_{\mathrm{med;causal}}(D_d) = |D_d|\,\mathbb E[\alpha_i^2 \mid i \in D_d]\,\mathbb E[h^2_{i,\mathrm{cis}} \mid i \in D_d]$.

**Assayed tissues.** If expression is measured in tissues $\mathcal T$ rather than the causal contexts, the estimable quantity is $h^2_{\mathrm{med;assayed}}(\mathcal T) = r_g^2(\mathcal T)\,h^2_{\mathrm{med;causal}}$, where $r_g^2(\mathcal T)$ is the average squared genetic correlation of cis-expression between $\mathcal T$ and the causal contexts; the remainder $(1 - r_g^2(\mathcal T))\,h^2_{\mathrm{med;causal}}$ is counted as non-mediated.

## Depends on

- [Genetic relationship matrix entry](../../quantitative-genetics/genomic-relationship-matrices/grm.md)

## Expansion

By the law of total variance, $\operatorname{Var}(XB\alpha) = \mathbb E[\operatorname{Var}(XB\alpha \mid B,\alpha)] + \operatorname{Var}(\mathbb E[XB\alpha\mid B,\alpha])$, and the second term vanishes because the standardized genotypes have mean zero. Conditionally on $B,\alpha$, the variance of the genetic value $\sum_j X_{\cdot j}\sum_i\beta_{ji}\alpha_i$ is taken as $\sum_i\alpha_i^2\sum_j\beta_{ji}^2$ (cross terms average out under independent, mean-zero effects), and $\sum_j\beta_{ji}^2$ is the cis-heritability of gene $i$; independence of $\alpha$ and $B$ splits the expectation into the product. Measuring expression in non-causal tissues attenuates the eQTL effects that can be correlated with the trait, which is why the assayed quantity is scaled by $r_g^2(\mathcal T)$.

## Sources

- D. W. Yao, L. J. O'Connor, A. L. Price et al., "Quantifying genetic effects on disease mediated by assayed gene expression levels", Nature Genetics (2020), Methods ("Definition of $h^2_{\mathrm{med}}$", "Unstratified MESC" with Equations 1–2, "Model assumptions", "Stratified MESC"), <https://doi.org/10.1038/s41588-020-0625-2> (PMC7276299).
