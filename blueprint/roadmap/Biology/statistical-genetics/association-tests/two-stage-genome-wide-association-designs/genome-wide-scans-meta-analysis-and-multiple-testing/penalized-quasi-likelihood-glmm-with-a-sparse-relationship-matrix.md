# Penalized quasi-likelihood fitting of a logistic mixed model with a sparse relationship matrix

Let $y \in \{0,1\}^n$ be a binary phenotype, $X_c$ an $n \times c$ matrix of covariates with fixed effects $\beta_c$, and $\pi$ an $n \times n$ relationship matrix (a pedigree matrix, or a genomic relationship matrix with all off-diagonal entries below a cutoff set to zero, hence sparse). The null generalized linear mixed model is

$$\mathrm{logit}(\mu) = X_c\beta_c + g, \qquad g \sim N(0, \pi\sigma_g^2), \qquad y_i \mid g \sim \mathrm{Bernoulli}(\mu_i).$$

The log quasi-likelihood of the null model is

$$\mathrm{ql}(\beta_c, \sigma_g^2) = \log\int \exp\Bigl(\sum_{i=1}^n \mathrm{ql}_i(\beta_c \mid g)\Bigr)(2\pi)^{-n/2}\bigl|\pi\sigma_g^2\bigr|^{-1/2}\exp\Bigl(-\tfrac12 g^\top(\pi\sigma_g^2)^{-1}g\Bigr)dg,$$

with $\mathrm{ql}_i(\beta_c \mid g) = \int_{y_i}^{\mu_i} (y_i - \mu)/(\mu(1-\mu))\,d\mu$ up to a known constant.

**Penalized quasi-likelihood solution.** With $W = \mathrm{diag}\{\mu_i(1 - \mu_i)\}$, $V = W^{-1} + \pi\sigma_g^2$ and the working vector $\tilde Y = X_c\beta_c + g + \mathrm{logit}'(\mu)(y - \mu)$, i.e. $\tilde Y_i = (X_c\beta_c + g)_i + (y_i - \mu_i)/(\mu_i(1-\mu_i))$,

$$\hat\beta_c = (X_c^\top V^{-1}X_c)^{-1}X_c^\top V^{-1}\tilde Y, \qquad \hat g = \sigma_g^2\,\pi\, V^{-1}(\tilde Y - X_c\hat\beta_c),$$

and the restricted (REML) quasi-likelihood is

$$\mathrm{ql}(\beta_c, \sigma_g^2) = \mathrm{const} - \tfrac12\log|V| - \tfrac12\log\bigl|X_c^\top V^{-1}X_c\bigr| - \tfrac12 \tilde Y^\top P \tilde Y, \qquad P = V^{-1} - V^{-1}X_c(X_c^\top V^{-1}X_c)^{-1}X_c^\top V^{-1}.$$

**Iteration (fastGWA-GLMM).** Start from the logistic-regression estimate $\hat\beta_{c(0)}$ with $\hat\sigma^2_{g(0)} = 0$ and $\hat g_0 = 0$; then repeat: form $\hat\mu_i$, $\tilde Y_i$, $W_i$; maximize the REML quasi-likelihood over $\sigma_g^2$; set $V_{i+1} = W_i^{-1} + \hat\sigma^2_{g(i+1)}\pi$ and update $\hat\beta_{c(i+1)}$, $\hat g_{i+1}$ by the two displayed formulas; stop when the relative changes of $\hat\beta_c$ and $\hat\sigma_g^2$ fall below a tolerance. Sparsity of $\pi$ makes $V$ sparse, so $|V|$ and $V^{-1}$ terms are computed by a sparse Cholesky decomposition, and $\sigma_g^2$ can be maximized by a nested grid search instead of average-information REML, which often fails to converge at extreme case-control ratios.

## Remarks

The working vector is the first-order Taylor expansion of the link at the current mean: $\mathrm{logit}(y) \approx \mathrm{logit}(\mu) + (y - \mu)/(\mu(1-\mu))$, so $\tilde Y$ behaves like a Gaussian response with heteroscedastic residual variance $W^{-1}$ and random effect $g$, hence total variance $V = W^{-1} + \pi\sigma_g^2$. The two update formulas are then the generalized-least-squares estimate of $\beta_c$ and the BLUP of $g$ in that linear mixed model, and the REML expression is the usual restricted log-likelihood of $\tilde Y$. Iterating this linearization is Breslow–Clayton penalized quasi-likelihood. It is known to bias $\hat\sigma_g^2$ for binary traits, so the fitted variance component is a nuisance quantity for controlling relatedness rather than an estimate of heritability. Once the null model is fitted, each variant is tested with the score statistic $T = x_s^\top(y - \hat\mu)$, whose variance $x_s^\top P x_s$ is approximated by a per-variant-free ratio estimated from a sample of variants, and small $p$-values are recalibrated by a saddlepoint approximation.

## Sources

- L. Jiang, Z. Zheng, H. Fang and J. Yang, "A generalized linear mixed model association tool for biobank-scale data", Nature Genetics 53 (2021), 1616–1621, Online Methods ("The fastGWA-GLMM method": null-model quasi-likelihood, PQL estimating equations, REML quasi-likelihood and the iteration steps 1–9; "The grid-search-based fastGWA-GLMM-REML optimizer"), <https://doi.org/10.1038/s41588-021-00954-4>.
