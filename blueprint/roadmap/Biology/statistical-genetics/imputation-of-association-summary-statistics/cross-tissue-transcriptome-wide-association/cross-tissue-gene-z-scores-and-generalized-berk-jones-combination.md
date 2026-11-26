# Cross-tissue gene-level z-scores and their generalized Berk–Jones combination

**Setting.** Let $\hat B \in \mathbb{R}^{M\times P}$ be cross-tissue expression weights for a gene (for example from [sparse group-lasso imputation](sparse-group-lasso-cross-tissue-expression-imputation.md)), and let a GWAS of sample size $N_{\mathrm{gwas}}$ report marginal SNP effects $\tilde\beta_j$ and $z$-scores $\tilde Z_j$ for the $M$ SNPs. Let $\sigma_j$ be the standard deviation of SNP $j$, $\eta_i$ the standard deviation of imputed expression in tissue $i$, $\Gamma_i = \operatorname{diag}(\sigma_1/\eta_i, \dots, \sigma_M/\eta_i)$, and $D$ the SNP correlation (LD) matrix, all estimated from a reference panel.

**Per-tissue statistic.** Regressing the trait $T$ on imputed expression $E_i = X\hat B_{\cdot i}$ gives slope $\hat\gamma_i = \hat B_{\cdot i}^\top \Gamma_i^2 \tilde\beta$. If each gene and each SNP explains a negligible share of trait variance, so that the residual variance is approximately the trait variance $\sigma_Y^2$, then $\operatorname{se}(\hat\gamma_i) \approx \sigma_Y/(\sqrt{N_{\mathrm{gwas}}}\,\eta_i)$ and $\tilde Z_j \approx \sqrt{N_{\mathrm{gwas}}}\,\sigma_j\tilde\beta_j/\sigma_Y$, hence

$$Z_i = \frac{\hat\gamma_i}{\operatorname{se}(\hat\gamma_i)} \approx \hat B_{\cdot i}^\top \Gamma_i\, \tilde Z .$$

**Joint null law.** Under no SNP–trait association $\tilde Z \sim \mathcal{N}(0, D)$, so $Z = (Z_1, \dots, Z_P)^\top = \Lambda^\top \tilde Z$ with $\Lambda = (\Gamma_1 \hat B_{\cdot 1}, \dots, \Gamma_P \hat B_{\cdot P})$ is approximately $\mathcal{N}(0, \Sigma)$ with

$$\Sigma = \Lambda^\top D \Lambda .$$

**Combination test.** With $|Z|_{(1)} \le \dots \le |Z|_{(P)}$ the ordered absolute statistics and $S(t) = \sum_{i=1}^{P}\mathbf{1}(|Z_i| \ge t)$, the generalized Berk–Jones statistic is

$$G = \max_{1 \le i \le P/2} \log\frac{\Pr\big(S(|Z|_{(P-i+1)}) = i \mid \mathbb{E}Z = \hat\mu_i,\ \operatorname{cov}Z = \Sigma\big)}{\Pr\big(S(|Z|_{(P-i+1)}) = i \mid \mathbb{E}Z = 0,\ \operatorname{cov}Z = \Sigma\big)}\ \mathbf{1}\big(2\bar\Phi(|Z|_{(P-i+1)}) < i/P\big),$$

a maximum of one-sided likelihood ratios for the mean of the exceedance count, where $\hat\mu_i$ maximizes the numerator and $\bar\Phi = 1 - \Phi$. Its $p$-value is computed under $Z \sim \mathcal{N}(0,\Sigma)$.

## Remarks

The approximation $Z_i \approx \hat B_{\cdot i}^\top\Gamma_i\tilde Z$ is the same summary-statistic identity used by single-tissue TWAS; it lets the whole test run on GWAS summary statistics plus a reference panel. Because expression weights in different tissues share SNPs and LD, the $Z_i$ are strongly correlated and $\Sigma$ is far from diagonal, which rules out naive Bonferroni or Fisher combination. The Berk–Jones family targets sparse alternatives (an effect in only a few tissues) while the generalization accounts for $\Sigma$; the source approximates the law of $S(t)$ under correlation by an extended beta-binomial distribution. Signs of $Z_i$ may differ across tissues, since only $|Z_i|$ enters.

## Depends on

- [Sparse group-lasso cross-tissue expression imputation](sparse-group-lasso-cross-tissue-expression-imputation.md)

## Sources

- Y. Hu, M. Li, Q. Lu, H. Weng et al., "A statistical framework for cross-tissue transcriptome-wide association analysis", Nature Genetics 51 (2019), 568–576, Online Methods ("Gene-level association test" and the generalized Berk–Jones test), <https://doi.org/10.1038/s41588-019-0345-7>, PMCID PMC6788740.
- R. Sun and X. Lin, "Genetic variant set-based tests using the generalized Berk–Jones statistic with application to a genome-wide association study of breast cancer", Journal of the American Statistical Association 115 (2020), <https://doi.org/10.1080/01621459.2019.1660170> (preprint: <https://arxiv.org/abs/1710.02469>).
