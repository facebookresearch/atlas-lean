# ComBat empirical Bayes location–scale batch adjustment

Let $Y_{ijg}$ be the expression value of gene $g$ for sample $j$ in batch $i$ ($i = 1, \dots, I$; $j = 1, \dots, n_i$), and let $X$ be a design matrix of biological covariates. The **location–scale model** is

$$Y_{ijg} = \alpha_g + X\beta_g + \gamma_{ig} + \delta_{ig}\,\varepsilon_{ijg}, \qquad \varepsilon_{ijg} \sim N(0, \sigma_g^2),$$

with additive batch effects $\gamma_{ig}$ and multiplicative batch effects $\delta_{ig} > 0$.

**Standardization.** Estimate $\hat\alpha_g$, $\hat\beta_g$ and raw-scale batch effects $\tilde\gamma_{ig}$ by gene-wise least squares, under the constraint $\sum_i n_i\tilde\gamma_{ig} = 0$, and set $\hat\sigma_g^2 = N^{-1}\sum_{ij}(Y_{ijg} - \hat\alpha_g - X\hat\beta_g - \tilde\gamma_{ig})^2$ with $N = \sum_i n_i$. The standardized data are $Z_{ijg} = (Y_{ijg} - \hat\alpha_g - X\hat\beta_g)/\hat\sigma_g$. Treating $\hat\alpha_g$, $\hat\beta_g$ and $\hat\sigma_g$ as fixed, ComBat models them as $Z_{ijg} \sim N(\gamma'_{ig}, \delta'^2_{ig})$ independently, where $\gamma'_{ig}$ and $\delta'_{ig} > 0$ are the **standardized** batch location and scale (not the raw $\gamma_{ig}$, $\delta_{ig}$ of the model above). The raw coefficients $\tilde\gamma_{ig}$ enter only through $\hat\sigma_g$; everything below uses only $Z$, so rescaling one gene leaves every other gene's adjustment unchanged.

**Gene-wise estimates.** From the standardized data of batch $i$ (with $n_i \ge 2$),

$$\hat\gamma'_{ig} = \frac{1}{n_i}\sum_{j=1}^{n_i} Z_{ijg}, \qquad \hat\delta'^2_{ig} = \frac{1}{n_i - 1}\sum_{j=1}^{n_i} \bigl(Z_{ijg} - \hat\gamma'_{ig}\bigr)^2 .$$

**Hierarchical prior.** Across genes within a batch, $\gamma'_{ig} \sim N(\gamma_i, \tau_i^2)$ and $\delta'^2_{ig} \sim \text{Inverse-Gamma}(\lambda_i, \theta_i)$. The hyperparameters are estimated by the method of moments from the standardized gene-wise estimates: $\bar\gamma_i, \bar\tau_i^2$ are the mean and variance of $\hat\gamma'_{ig}$ over $g$, and $\bar\lambda_i, \bar\theta_i$ match the mean and variance of $\hat\delta'^2_{ig}$ over $g$ (assumed to have positive variance, so that $\bar\lambda_i > 2$).

**Empirical Bayes estimates.** The conditional posterior means are

$$\gamma_{ig}^* = \frac{n_i \bar\tau_i^2\, \hat\gamma'_{ig} + \delta_{ig}^{*2}\, \bar\gamma_i}{n_i \bar\tau_i^2 + \delta_{ig}^{*2}}, \qquad \delta_{ig}^{*2} = \frac{\bar\theta_i + \tfrac12 \sum_j (Z_{ijg} - \gamma_{ig}^*)^2}{\tfrac{n_i}{2} + \bar\lambda_i - 1},$$

solved jointly by iteration.

**Adjusted data.**

$$Y_{ijg}^* = \frac{\hat\sigma_g}{\delta_{ig}^*}\bigl(Z_{ijg} - \gamma_{ig}^*\bigr) + \hat\alpha_g + X\hat\beta_g .$$

The posterior means shrink the noisy gene-wise standardized batch estimates towards the batch-wide means, which keeps the adjustment stable for small batches.

## Expansion

Given $\delta'^2_{ig}$, the normal prior on $\gamma'_{ig}$ is conjugate to the $n_i$ normal observations $Z_{ijg}$, whose sufficient statistic is $\hat\gamma'_{ig}$. The posterior mean is therefore the precision-weighted average of $\hat\gamma'_{ig}$ (precision $n_i/\delta'^2_{ig}$) and $\bar\gamma_i$ (precision $1/\bar\tau_i^2$); substituting the current value $\delta^{*2}_{ig}$ for $\delta'^2_{ig}$ gives the displayed $\gamma^*$. Given $\gamma'_{ig}$, the inverse-gamma prior is conjugate for the variance of normal data. Its posterior is $\text{Inverse-Gamma}(\lambda_i + n_i/2,\ \theta_i + \tfrac12\sum_j (Z_{ijg} - \gamma'_{ig})^2)$, whose mean, at $\gamma'_{ig} = \gamma^*_{ig}$, is the displayed $\delta^{*2}$. Iterating the two conditional means gives a joint fixed point.

## Sources

- W. E. Johnson, C. Li and A. Rabinovic, *Adjusting batch effects in microarray expression data using empirical Bayes methods*, Biostatistics 8 (2007), 118–127, <https://doi.org/10.1093/biostatistics/kxj037> (the location–scale model, standardization, hierarchical priors, empirical Bayes estimators and adjusted data; the supplementary material and the `ComBat` function of the Bioconductor `sva` package estimate the priors and conditional means from the batch means and variances of the standardized data).
