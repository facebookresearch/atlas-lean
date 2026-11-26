# LD correction of the cross-population genetic correlation

**Model.** In population $k \in \{1, 2\}$ let $X_{A,k}$ be the $N_k \times M$ matrix of mean-centred genotypes at all $M$ SNPs and $X_{G,k}$ its columns at a fixed set of $M_G$ genotyped SNPs. Under the additive infinitesimal model $Y_k = X_{A,k} b_k + e_{b,k}$, with causal effects $b_k \sim N(0, \sigma_k^2 I_M)$ and $\mathbb{E}[b_1 b_2^\top] = \rho_b \sigma_1 \sigma_2 I_M$, the joint-fit effects at genotyped SNPs are the large-sample regression coefficients

$$g_k = \lim_{N_k \to \infty} (X_{G,k}^\top X_{G,k})^{-1} X_{G,k}^\top Y_k = S^{(k)\,-1}_{GG} S^{(k)}_{GA}\, b_k,$$

where $S^{(k)}$ is the SNP covariance matrix in population $k$, partitioned into genotyped ($G$) and all ($A$) SNPs, with $S^{(k)}_{GG}$ invertible. Write $M_k = S^{(k)\,-1}_{GG} S^{(k)}_{GA}$, an $M_G \times M$ matrix, so that $g_k = M_k b_k$. Define the genetic correlation at causal SNPs $\rho_b$ as above and at genotyped SNPs

$$\rho_g = \frac{\mathbb{E}[g_1^\top g_2]}{\sqrt{\mathbb{E}[g_1^\top g_1]\,\mathbb{E}[g_2^\top g_2]}}.$$

**Theorem.** With

$$\tau(S_1, S_2) = \frac{\mathrm{tr}(S_1 S_2^\top)}{\sqrt{\mathrm{tr}(S_1 S_1^\top)\, \mathrm{tr}(S_2 S_2^\top)}},$$

and $M_1, M_2 \neq 0$, the two correlations satisfy

$$\rho_g = \rho_b\, \tau(M_1, M_2).$$

Hence, given $\tau(M_1, M_2) \neq 0$, an estimate $\hat\rho_g$ (by bivariate REML or from summary statistics) is corrected to $\hat\rho_b = \hat\rho_g / \tau(\hat M_1, \hat M_2)$, with $\hat M_k$ computed from reference-panel LD in population $k$. By Cauchy–Schwarz $|\tau(M_1, M_2)| \le 1$, so the correction never shrinks $|\hat\rho_g|$; it is the identity when $M_1 = M_2$.

## Proof sketch

Since $g_k = M_k b_k$ and $\mathbb{E}[b_1 b_2^\top] = \rho_b \sigma_1 \sigma_2 I_M$, the trace identity gives $\mathbb{E}[g_1^\top g_2] = \mathrm{tr}\bigl(M_1\, \mathbb{E}[b_1 b_2^\top]\, M_2^\top\bigr) = \rho_b \sigma_1 \sigma_2\, \mathrm{tr}(M_1 M_2^\top)$, and likewise $\mathbb{E}[g_k^\top g_k] = \sigma_k^2\, \mathrm{tr}(M_k M_k^\top)$. Dividing gives the theorem. The source instead approximates the correlation of $S^{(k)}_{GG} g_k = S^{(k)}_{GA} b_k$ by two separate trace ratios, $\rho_g\, \tau(S^{(1)}_{GG}, S^{(2)}_{GG}) \approx \rho_b\, \tau(S^{(1)}_{GA}, S^{(2)}_{GA})$, which treats $g_k$ as having isotropic covariance; that heuristic gives $\rho_g/\rho_b \approx \tau(S^{(1)}_{GA}, S^{(2)}_{GA}) / \tau(S^{(1)}_{GG}, S^{(2)}_{GG})$, and it is exact only under that extra isotropy assumption. In the source's approximation the traces are of raw covariance (LD) matrices, and since $\mathrm{tr}(S_1^\top S_2) = \sum_{i,j} S^{(1)}_{ij} S^{(2)}_{ij}$ they are sums of (cross-population) LD scores estimable from reference panels; because sample squared correlations are biased upward, each $\hat r^2_{ij}$ is replaced by $\hat r^2_{ij} - (1 - \hat r^2_{ij})/(N_k - 2)$, and LD is restricted to 1 Mb windows. That entrywise calculation and adjustment do not apply to the exact identity: the entries of $M_k = S^{(k)\,-1}_{GG} S^{(k)}_{GA}$ are joint regression coefficients, not raw correlations. For instance, if every SNP is genotyped then $M_k = I$ for every invertible $S^{(k)}_{GG}$, including one with nonzero off-diagonal LD, so $\mathrm{tr}(M_k M_k^\top)$ is the number of SNPs, not a sum of raw LD scores. For the exact identity one computes $\hat M_1, \hat M_2$ from the reference panels and their Frobenius products $\mathrm{tr}(\hat M_1 \hat M_2^\top)$, $\mathrm{tr}(\hat M_k \hat M_k^\top)$ directly; the $r^2$ bias adjustment is not claimed to debias these.

## Sources

- K. J. Galinsky, Y. A. Reshef, H. K. Finucane et al., "Estimating cross-population genetic correlations of causal effect sizes", Genetic Epidemiology 43 (2019), 180–188, <https://doi.org/10.1002/gepi.22173>, PMCID PMC6375794. Materials and Methods, "Genotype-phenotype model" and "Estimating $\rho_g/\rho_b$".
