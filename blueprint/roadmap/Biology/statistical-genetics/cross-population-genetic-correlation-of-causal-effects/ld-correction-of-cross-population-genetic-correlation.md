# LD correction of the cross-population genetic correlation

**Model.** In population $k \in \{1, 2\}$ let $X_{A,k}$ be the $N_k \times M$ matrix of mean-centred genotypes at all $M$ SNPs and $X_{G,k}$ its columns at a fixed set of $M_G$ genotyped SNPs. Under the additive infinitesimal model $Y_k = X_{A,k} b_k + e_{b,k}$, with causal effects $b_k \sim N(0, \sigma_k^2 I_M)$ and $\mathbb{E}[b_1 b_2^\top] = \rho_b \sigma_1 \sigma_2 I_M$, the joint-fit effects at genotyped SNPs are the large-sample regression coefficients

$$g_k = \lim_{N_k \to \infty} (X_{G,k}^\top X_{G,k})^{-1} X_{G,k}^\top Y_k = S^{(k)\,-1}_{GG} S^{(k)}_{GA}\, b_k,$$

where $S^{(k)}$ is the SNP covariance matrix in population $k$, partitioned into genotyped ($G$) and all ($A$) SNPs. Define the cross-population genetic correlation at genotyped SNPs $\rho_g = \mathrm{corr}(g_1, g_2)$ and at causal SNPs $\rho_b = \mathrm{corr}(b_1, b_2)$.

**Theorem.** With

$$\tau(S_1, S_2) = \frac{\mathrm{tr}(S_1 S_2^\top)}{\sqrt{\mathrm{tr}(S_1 S_1^\top)\, \mathrm{tr}(S_2 S_2^\top)}},$$

the two correlations satisfy

$$\frac{\rho_g}{\rho_b} = \frac{\tau\bigl(S^{(1)}_{GG}, S^{(2)}_{GG}\bigr)}{\tau\bigl(S^{(1)}_{GA}, S^{(2)}_{GA}\bigr)}.$$

Since $\mathrm{tr}(S_1^\top S_2) = \sum_{i,j} S^{(1)}_{ij} S^{(2)}_{ij}$, the denominators of $\tau$ are sums of LD scores and the numerator is a sum of cross-population LD scores, all estimable from a reference panel. Estimating $\rho_g$ (by bivariate REML or from summary statistics) and dividing by this ratio gives an estimate of $\rho_b$.

## Expansion

From $S_{GG}^{(k)} g_k = S_{GA}^{(k)} b_k$ the vectors $S^{(1)}_{GG} g_1$ and $S^{(2)}_{GG} g_2$ have the same correlation as $S^{(1)}_{GA} b_1$ and $S^{(2)}_{GA} b_2$. For the latter, the trace trick gives $\mathrm{Cov} = \mathrm{tr}\bigl(S^{(1)}_{GA}\, \mathbb{E}[b_1 b_2^\top]\, S^{(2)\top}_{GA}\bigr) = \rho_b \sigma_1 \sigma_2\, \mathrm{tr}(S^{(1)}_{GA} S^{(2)\top}_{GA})$ and similarly for the variances, so that correlation equals $\rho_b\, \tau(S^{(1)}_{GA}, S^{(2)}_{GA})$. Applying the same identity to the $g_k$, treated as random effects with covariance structure induced by the infinitesimal model, gives $\rho_g\, \tau(S^{(1)}_{GG}, S^{(2)}_{GG})$, and equating the two yields the ratio. Because the sample squared correlations are biased upward, each $\hat r^2_{ij}$ is replaced by $\hat r^2_{ij} - (1 - \hat r^2_{ij})/(N_k - 2)$, and LD is restricted to 1 Mb windows. When LD differs between populations $\rho_g < \rho_b$ typically, so uncorrected genotyped-SNP correlations understate how similar causal effects are.

## Sources

- K. J. Galinsky, Y. A. Reshef, H. K. Finucane et al., "Estimating cross-population genetic correlations of causal effect sizes", Genetic Epidemiology 43 (2019), 180–188, <https://doi.org/10.1002/gepi.22173>, PMCID PMC6375794. Materials and Methods, "Genotype-phenotype model" and "Estimating $\rho_g/\rho_b$".
