# Summary-MultiXcan chi-square test from single-tissue Z-scores

In the setting of [MultiXcan](multixcan-joint-regression-on-principal-components.md), suppose only single-tissue association $Z$-scores $\hat z = (\hat z_1, \dots, \hat z_p)$, $\hat z_j = \hat\gamma_j/\mathrm{se}(\hat\gamma_j)$, are available, together with a reference panel giving the SNP covariance $\Gamma$ restricted to SNPs present in both the GWAS and the panel. The correlation of predicted expression between tissues $i$ and $j$ is

$$\mathrm{Cor}(t_i, t_j) = \frac{\sum_{a \in \mathrm{model}_i}\sum_{b \in \mathrm{model}_j} w_{ai} w_{bj}\Gamma_{ab}}{\hat\sigma_i\hat\sigma_j}, \qquad \hat\sigma_j^2 = W_j^\top\Gamma W_j. \tag{9, 10}$$

Under $H_0: g = 0$ and approximate normality, $\hat g^\top (T^\top T)\hat g/\sigma_e^2 \sim \chi^2_p$. Approximating the joint residual variance by the marginal one, $\sigma_e^2 \approx \sigma_\epsilon^2$, gives

$$\frac{\hat g^\top (T^\top T)\hat g}{\sigma_e^2} \approx \hat z^\top \mathrm{Cor}(T)^{-1}\hat z.$$

**S-MultiXcan statistic.** Replace $\mathrm{Cor}(T)^{-1}$ by the pseudo-inverse $\mathrm{Cor}(T)^{+}$ that keeps the eigen-directions with $\lambda_{\max}/\lambda_i < 30$, and refer

$$\hat z^\top\,\mathrm{Cor}(T)^{+}\,\hat z \sim \chi^2_k$$

to a chi-square distribution with $k$ degrees of freedom, $k$ the number of retained eigen-directions.

## Remarks

From $\hat g = (T^\top T)^{-1}D\hat\gamma$, the quadratic form is $\hat\gamma^\top D (T^\top T)^{-1} D\hat\gamma/\sigma_e^2$. With standardized predictors $D = (n-1)I$ and $T^\top T = (n-1)\mathrm{Cor}(T)$, and $\mathrm{se}(\hat\gamma_j) = \sigma_\epsilon/\sqrt{n-1}$, this equals $(\sigma_\epsilon/\sigma_e)^2\,\hat z^\top\mathrm{Cor}(T)^{-1}\hat z$. Using $\sigma_e^2 \approx \sigma_\epsilon^2$ is conservative, since joint residual variance is at most the marginal one. If $\hat z \sim N(0, \mathrm{Cor}(T))$ under the null, then for the spectral pseudo-inverse $P^\top \Lambda_k^{-1} P$ on $k$ directions the statistic is a sum of $k$ independent squared standard normals. The covariance formula is the variance of a linear combination of genotypes, $\mathrm{Cov}(X W_i, X W_j) = W_i^\top\Gamma W_j$, normalized. Using panel SNPs absent from the GWAS would misstate the correlation and inflate false positives.

## Depends on

- [MultiXcan joint regression on principal components of predicted expression](multixcan-joint-regression-on-principal-components.md)

## Sources

- A. N. Barbeira, M. Pividori, J. Zheng et al., "Integrating predicted transcriptome from multiple tissues improves association detection", PLoS Genetics 15 (2019), e1007889, Materials and Methods ("Summary-MultiXcan": "Estimating expression correlation from a reference panel", Equations (9)–(10); "Addressing singularity of the correlation matrix"; "Estimating significance"), <https://doi.org/10.1371/journal.pgen.1007889>, PMCID PMC6358100.
