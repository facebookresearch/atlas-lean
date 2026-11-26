# ComBat empirical Bayes location–scale batch adjustment

Let $Y_{ijg}$ be the expression value of gene $g$ for sample $j$ in batch $i$ ($i = 1, \dots, I$; $j = 1, \dots, n_i$), and let $X$ be a design matrix of biological covariates. The **location–scale model** is

$$Y_{ijg} = \alpha_g + X\beta_g + \gamma_{ig} + \delta_{ig}\,\varepsilon_{ijg}, \qquad \varepsilon_{ijg} \sim N(0, \sigma_g^2),$$

with additive batch effects $\gamma_{ig}$ and multiplicative batch effects $\delta_{ig} > 0$.

**Standardization.** Estimate $\hat\alpha_g$, $\hat\beta_g$ and $\hat\gamma_{ig}$ by gene-wise least squares, under the constraint $\sum_i n_i\hat\gamma_{ig} = 0$, and set $\hat\sigma_g^2 = N^{-1}\sum_{ij}(Y_{ijg} - \hat\alpha_g - X\hat\beta_g - \hat\gamma_{ig})^2$. The standardized data are $Z_{ijg} = (Y_{ijg} - \hat\alpha_g - X\hat\beta_g)/\hat\sigma_g$, and $Z_{ijg} \sim N(\gamma_{ig}, \delta_{ig}^2)$.

**Hierarchical prior.** Across genes within a batch, $\gamma_{ig} \sim N(\gamma_i, \tau_i^2)$ and $\delta_{ig}^2 \sim \text{Inverse-Gamma}(\lambda_i, \theta_i)$. The hyperparameters are estimated by the method of moments from the gene-wise estimates: $\bar\gamma_i, \bar\tau_i^2$ are the mean and variance of $\hat\gamma_{ig}$ over $g$, and $\bar\lambda_i, \bar\theta_i$ match the mean and variance of the sample variances $\hat\delta_{ig}^2$.

**Empirical Bayes estimates.** The conditional posterior means are

$$\gamma_{ig}^* = \frac{n_i \bar\tau_i^2\, \hat\gamma_{ig} + \delta_{ig}^{*2}\, \bar\gamma_i}{n_i \bar\tau_i^2 + \delta_{ig}^{*2}}, \qquad \delta_{ig}^{*2} = \frac{\bar\theta_i + \tfrac12 \sum_j (Z_{ijg} - \gamma_{ig}^*)^2}{\tfrac{n_i}{2} + \bar\lambda_i - 1},$$

solved jointly by iteration.

**Adjusted data.**

$$Y_{ijg}^* = \frac{\hat\sigma_g}{\delta_{ig}^*}\bigl(Z_{ijg} - \gamma_{ig}^*\bigr) + \hat\alpha_g + X\hat\beta_g .$$

The posterior means shrink the noisy gene-wise batch estimates towards the batch-wide means, which keeps the adjustment stable for small batches.

## Expansion

Given $\delta_{ig}^2$, the normal prior on $\gamma_{ig}$ is conjugate to the $n_i$ normal observations $Z_{ijg}$. The posterior mean is therefore the precision-weighted average of $\hat\gamma_{ig}$ (precision $n_i/\delta_{ig}^2$) and $\bar\gamma_i$ (precision $1/\bar\tau_i^2$), which is the displayed $\gamma^*$. Given $\gamma_{ig}$, the inverse-gamma prior is conjugate for the variance of normal data. Its posterior is $\text{Inverse-Gamma}(\lambda_i + n_i/2,\ \theta_i + \tfrac12\sum_j (Z_{ijg} - \gamma_{ig})^2)$, whose mean is the displayed $\delta^{*2}$. Iterating the two conditional means gives a joint fixed point.

## Sources

- W. E. Johnson, C. Li and A. Rabinovic, *Adjusting batch effects in microarray expression data using empirical Bayes methods*, Biostatistics 8 (2007), 118–127, <https://doi.org/10.1093/biostatistics/kxj037> (the location–scale model, standardization, hierarchical priors, empirical Bayes estimators and adjusted data).
