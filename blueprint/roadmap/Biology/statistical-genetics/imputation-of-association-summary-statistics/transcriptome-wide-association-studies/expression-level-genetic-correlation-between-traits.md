# Genetic correlation between traits at the level of predicted expression

Model a trait as the sum of effects mediated through the cis-regulated expression of $k$ genes and other genetic effects:

$$y_T = \sum_{i=1}^{k}(X_i\beta_{GE_i})\,\alpha_i + X_{\mathrm{alt}}\beta_{\mathrm{alt}} + \epsilon_T,$$

where $X_i$ are the genotypes in the cis-region of gene $i$, $\beta_{GE_i}$ its causal eQTL effects, $\alpha_i$ the effect of its expression on the trait, and $X_{\mathrm{alt}}\beta_{\mathrm{alt}}$ the effects not mediated by expression. For two traits $T_1, T_2$ the **expression-level genetic correlation** is the correlation of gene effects across genes,

$$\rho_{GE} = \operatorname{cor}(\alpha^{T_1}, \alpha^{T_2}).$$

**Estimation.** Each gene effect is estimated from summary data by regressing the trait on predicted expression,

$$\hat\alpha_i = \frac{\operatorname{cov}(X_i\beta_{GE_i}, y_T)}{\operatorname{var}(X_i\beta_{GE_i})} = \frac{\beta_{GE_i}^\top V_i\beta_T}{h^2_{g,\mathrm{local}}(GE_i)},$$

which is proportional to the [local expression–trait genetic correlation](local-genetic-correlation-between-expression-and-trait.md) (in practice the standardized estimates are used). $\hat\rho_{GE}$ is the sample correlation of the standardized estimates over $M$ genes, taking one gene per 1 Mb locus so the gene effects are approximately independent, and $\hat\rho_{GE}\sqrt{(M-2)/(1-\hat\rho_{GE}^2)}$ is referred to a $t_{M-2}$ distribution.

**Directional comparison.** Estimating $\rho_{GE}$ on the genes ascertained for trait $i$ (giving $\rho_{j\mid i}$) and on those ascertained for trait $j$ (giving $\rho_{i\mid j}$) and comparing them with Welch's $t$ test discriminates the causal models $T_1 \to T_2$ and $T_2 \to T_1$, but cannot exclude a shared pathway driving both traits.

## Remarks

$\rho_{GE}$ differs from the SNP-based genetic correlation $\rho_g$: $\rho_g$ correlates total SNP effects $\beta_{GE}\alpha + \beta_{\mathrm{alt}}$, whereas $\rho_{GE}$ correlates only the expression effects $\alpha$, so traits sharing cis-mediated mechanisms but not trans effects have $\rho_{GE} > \rho_g$, and $\rho_{GE} \approx \rho_g$ when trans-eQTL effects are small. If $T_1$ causes $T_2$ with effect $\gamma$, the genes driving $T_1$ have effects $\beta_{T_1}\gamma$ on $T_2$, so the correlation computed on $T_1$'s genes is non-zero, whereas genes specific to $T_2$ have no effect on $T_1$; this asymmetry is what the conditional comparison detects.

## Depends on

- [Local genetic correlation between gene expression and a trait from a TWAS statistic](local-genetic-correlation-between-expression-and-trait.md)
- [Unbiased local SNP heritability from GWAS summary statistics](../../greml-and-haseman-elston-estimation-of-snp-herit/local-snp-heritability-from-summary-statistics/unbiased-local-snp-heritability-from-gwas-summary-statistics.md)

## Sources

- N. Mancuso, H. Shi, P. Goddard et al., "Integrating gene expression with summary association statistics to identify genes associated with 30 complex traits", American Journal of Human Genetics 100 (2017), 473–487, Material and Methods ("Estimating Genetic Correlation of Expression and Complex Traits from Summary Data", "Genetic Correlation between Traits at the Level of Predicted Expression"), <https://doi.org/10.1016/j.ajhg.2017.01.031> (PMC5339290).
