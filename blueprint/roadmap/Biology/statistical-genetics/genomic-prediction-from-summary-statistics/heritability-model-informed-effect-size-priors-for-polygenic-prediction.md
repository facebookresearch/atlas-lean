# Heritability-model-informed effect-size priors for polygenic prediction

**Model.** Phenotypes follow $Y \sim \mathcal{N}(X\beta, \sigma_e^2 I)$ for standardized genotypes $X$ of $m$ SNPs. Let $e_j$ be an estimate of $\mathbb{E}[h_j^2]$, the expected heritability of SNP $j$ under a chosen heritability model (for example from [SumHer](sumher-expected-association-statistics-under-a-heritability-model.md)), and set $\sigma_e^2 = 1 - \sum_j e_j$. Each prior family scales SNP $j$ by $e_j$:

- lasso: $\beta_j \sim \mathrm{DE}\big(\lambda/\sqrt{e_j}\big)$ (double exponential);
- ridge: $\beta_j \sim \mathcal{N}(0, v\,e_j)$ ($v = 1$ with individual-level data);
- Bolt: $\beta_j \sim p\,\mathcal{N}\!\big(0, \tfrac{1-f^2}{p}e_j\big) + (1-p)\,\mathcal{N}\!\big(0, \tfrac{f^2}{1-p}e_j\big)$;
- BayesR: $\beta_j \sim \pi_1\delta_0 + \pi_2\mathcal{N}(0, s e_j/100) + \pi_3\mathcal{N}(0, s e_j/10) + \pi_4\mathcal{N}(0, s e_j)$, with $\sum_i\pi_i = 1$ and $s = (\pi_2/100 + \pi_3/10 + \pi_4)^{-1}$.

For the individual-level ridge, Bolt and BayesR priors $\mathbb{E}[\beta_j^2] = e_j$ (the normalizing constants $p$, $1-p$ and $s$ are chosen for this), so the prior variance of each effect matches its expected heritability; in all families the relative shrinkage of SNPs follows $e_j$, and the GCTA Model ($e_j$ constant) recovers the standard tools (lasso, BLUP, Bolt-LMM, BayesR). The remaining hyperparameters ($\lambda$, $v$, $p$, $f^2$, $\pi$) are chosen by cross-validation. With individual-level data, the lasso is fitted by coordinate descent with warm starts (each update replaces $\beta_j$ by its conditional posterior mode) and the ridge, Bolt and BayesR priors by variational Bayes (each update replaces $\beta_j$ by its conditional posterior mean). With summary statistics and a reference LD panel, all four priors, the lasso included, are fitted by variational Bayes with conditional posterior means, run over sliding genomic windows.

## Remarks

For the Bolt prior, $p\cdot\frac{1-f^2}{p}e_j + (1-p)\cdot\frac{f^2}{1-p}e_j = e_j$; for BayesR, $s(\pi_2/100 + \pi_3/10 + \pi_4)e_j = e_j$. The ridge case is the Bolt prior at $p = f^2 = 1/2$. Standard tools implicitly assume every SNP contributes equal heritability; letting the prior variance follow $e_j$ shrinks SNPs in low-heritability classes (for example low-frequency or high-LD SNPs under the LDAK-type models) more strongly. In the source, replacing the GCTA Model by the BLD-LDAK Model raised the prediction $R^2$ for all eight tools: by about 14% on average for the Bolt prior with individual-level data (equivalent to roughly 24% more training samples), and the summary-statistic BayesR variant outperformed the existing summary-statistic tools for 223 of 225 UK Biobank phenotypes.

## Depends on

- [SumHer: expected association statistics under an annotation-based heritability model](sumher-expected-association-statistics-under-a-heritability-model.md)
- [Two-Gaussian mixture prior on a SNP effect](../bolt-lmm-mixed-model-association/mixture-prior.md)

## Sources

- Q. Zhang, F. Privé, B. Vilhjálmsson and D. Speed, "Improved genetic prediction of complex traits from individual-level data or summary statistics", Nature Communications 12 (2021), 4192, Methods ("New prediction tools", "Model fitting using individual-level data", "Model fitting using summary statistics", Equations (1) and (4)), <https://doi.org/10.1038/s41467-021-24485-y>, PMCID PMC8263809.
