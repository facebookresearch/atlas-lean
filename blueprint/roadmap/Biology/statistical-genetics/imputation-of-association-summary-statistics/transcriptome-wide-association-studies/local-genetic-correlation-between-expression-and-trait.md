# Local genetic correlation between gene expression and a trait from a TWAS statistic

In a cis-region of about 1 Mb around a gene, let $X$ be standardized genotypes with LD matrix $V$ (assumed invertible), and model expression and trait as $y_{GE} = X\beta_{GE} + \epsilon_{GE}$ and $y_T = X\beta_T + \epsilon_T$ with standardized effects, measured in non-overlapping samples of sizes $N_{GE}$ and $N_T$ (so $\operatorname{cov}(\epsilon_{GE},\epsilon_T) = 0$). The local genetic covariance is $\beta_{GE}^\top V\beta_T$ and the local genetic correlation is

$$\rho_{g,\mathrm{local}} = \frac{\beta_{GE}^\top V\beta_T}{\sqrt{h^2_{g,\mathrm{local}}(GE)\,h^2_{g,\mathrm{local}}(T)}},$$

with $h^2_{g,\mathrm{local}}$ the local SNP heritabilities.

**Estimator.** With GWAS z-scores $z_T$, the LD-adjusted trait effects are $\hat\beta_T = N_T^{-1/2}V^{-1}z_T$, and with expression weights $w_{GE} = \hat\beta_{GE}$ the TWAS statistic is

$$z_{\mathrm{TWAS}} = \frac{w_{GE}^\top z_T}{\sqrt{w_{GE}^\top V w_{GE}}}.$$

Taking $w_{GE}^\top V w_{GE}$ as the local expression heritability, $z_{\mathrm{TWAS}}/\sqrt{N_T} = \hat\beta_{GE}^\top V\hat\beta_T / \sqrt{h^2_{g,\mathrm{local}}(GE)}$, which estimates $\rho_{g,\mathrm{local}}\sqrt{h^2_{g,\mathrm{local}}(T)}$. Hence

$$\hat\rho_{g,\mathrm{local}} = \frac{z_{\mathrm{TWAS}}}{\sqrt{N_T\,h^2_{g,\mathrm{local}}(T)}},$$

where in practice the variance explained by the locus's lead SNP is used for $h^2_{g,\mathrm{local}}(T)$.

## Remarks

$\operatorname{cov}(y_{GE}, y_T) = \beta_{GE}^\top\operatorname{cov}(X,X)\beta_T + \operatorname{cov}(\epsilon_{GE},\epsilon_T) = \beta_{GE}^\top V\beta_T$ for standardized genotypes and independent samples. With marginal standardized effect estimates $\hat b = z/\sqrt N$, the plug-in covariance is $\hat\beta_{GE}^\top V\hat\beta_T = \hat b_{GE}^\top V^{-1}\hat b_T$, the LD-adjusted covariance of marginal effects. Dividing the TWAS z-score by $\sqrt{N_T}$ turns it into this covariance normalized by the predicted-expression standard deviation, so one further division by the trait's local heritability gives a correlation. The sign of $\hat\rho_{g,\mathrm{local}}$ gives the direction of the expression–trait relationship at the locus.

## Depends on

- [In-sample LD matrix](../../genomic-prediction-from-summary-statistics/ld-matrix.md)
- [Unbiased local SNP heritability from GWAS summary statistics](../../greml-and-haseman-elston-estimation-of-snp-herit/local-snp-heritability-from-summary-statistics/unbiased-local-snp-heritability-from-gwas-summary-statistics.md)

## Sources

- N. Mancuso, H. Shi, P. Goddard et al., "Integrating gene expression with summary association statistics to identify genes associated with 30 complex traits", American Journal of Human Genetics 100 (2017), 473–487, Material and Methods ("Estimating Genetic Correlation of Expression and Complex Traits from Summary Data", "Genetic Correlation between Traits at the Level of Predicted Expression"), <https://doi.org/10.1016/j.ajhg.2017.01.031> (PMC5339290).
