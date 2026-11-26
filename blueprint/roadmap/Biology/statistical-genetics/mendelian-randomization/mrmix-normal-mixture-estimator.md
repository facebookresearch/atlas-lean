# MRMix normal-mixture Mendelian randomization estimator

**Model.** For an exposure $X$ and an outcome $Y$ with causal effect $\theta$, each SNP has direct effects $(u_x, u_y)$ and total effects $\beta_x = u_x$, $\beta_y = u_y + \theta u_x$. SNPs fall into four classes with probabilities $\pi_1, \dots, \pi_4$:

1. valid instruments: $u_x \sim N(0, \sigma_x^2)$, $u_y = 0$;
2. correlated horizontal pleiotropy: $(u_x, u_y)$ bivariate normal with variances $\sigma_x^2, \sigma_y^2$ and covariance $\sigma_{xy}$ (so the InSIDE assumption may fail);
3. outcome-only effects: $u_x = 0$, $u_y \sim N(0, \sigma_y^2)$;
4. null SNPs: $u_x = u_y = 0$.

GWAS estimates satisfy $\hat\beta_x \sim N(\beta_x, s_x^2)$ and $\hat\beta_y \sim N(\beta_y, s_y^2)$ with known standard errors. Since $u_y = 0$ in classes 1 and 4 and is continuous otherwise, the modal pleiotropic effect is $0$ (the zero modal pleiotropy assumption).

**Residual law.** At the true $\theta$,

$$\hat\beta_y - \theta \hat\beta_x \sim (\pi_1 + \pi_4)\, N(0, s_y^2 + \theta^2 s_x^2) + (\pi_2 + \pi_3)\, N(0, \sigma_y^2 + s_y^2 + \theta^2 s_x^2),$$

whereas at $\tilde\theta \ne \theta$ the valid instruments acquire the extra variance $(\theta - \tilde\theta)^2 \sigma_x^2$ and only the mass $\pi_4$ remains at $N(0, s_y^2 + \tilde\theta^2 s_x^2)$.

**Estimator.** For each $\tilde\theta$ on a grid, fit by maximum likelihood the two-component mixture

$$\hat\beta_y - \tilde\theta \hat\beta_x \sim \pi_0\, N(0, s_y^2 + \tilde\theta^2 s_x^2) + (1 - \pi_0)\, N(0, \sigma^2)$$

in the unknowns $(\pi_0, \sigma^2)$, and set

$$\hat\theta = \arg\max_{\tilde\theta} \hat\pi_0(\tilde\theta).$$

## Remarks

The residual $\hat\beta_y - \tilde\theta\hat\beta_x$ of a valid instrument is pure estimation noise exactly when $\tilde\theta = \theta$; for any other value it carries the term $(\theta - \tilde\theta) u_x$, which spreads it out. Thus the probability mass concentrated at the null component is largest, $\pi_1 + \pi_4$ instead of $\pi_4$, at the true causal effect, and maximizing the fitted null weight solves a spike-detection problem rather than a full mixture likelihood in all of $(\pi_1, \pi_2, \pi_3, \sigma_x^2, \sigma_y^2, \sigma_{xy})$. The two-component working model is correct only at $\tilde\theta = \theta$, which is all the argmax needs. Like the mode-based estimator it tolerates a majority of invalid instruments as long as the valid ones form the largest concentration, and it permits correlated pleiotropy because class-2 SNPs never collapse onto the null component.

## Sources

- G. Qi and N. Chatterjee, "Mendelian randomization analysis using mixture models for robust and efficient estimation of causal effects", Nature Communications 10 (2019), <https://doi.org/10.1038/s41467-019-09432-2>, PMCID PMC6486646. Methods, "Model" and "MR analysis using mixture-model (MRMix)".
