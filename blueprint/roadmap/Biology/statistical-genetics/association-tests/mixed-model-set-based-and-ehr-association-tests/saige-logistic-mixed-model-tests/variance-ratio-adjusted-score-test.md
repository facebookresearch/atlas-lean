# Variance-ratio adjusted score test in a logistic mixed model

Let $N$ individuals have binary phenotypes $y_i \in \{0, 1\}$, covariate rows $X_i \in \mathbb{R}^{1 \times (1+p)}$ (including an intercept) and allele counts $G_i \in \{0, 1, 2\}$ at a tested variant. The logistic mixed model is

$$\operatorname{logit}(\mu_i) = X_i \alpha + G_i \beta + b_i, \qquad b \sim N(0, \tau \Psi),$$

where $\mu_i = \Pr(y_i = 1 \mid X_i, G_i, b_i)$ and $\Psi$ is an $N \times N$ genetic relationship matrix. Fit the null model $\beta = 0$ (by penalized quasi-likelihood and AI-REML) to obtain $\hat\mu$, $\hat W = \operatorname{diag}\{\hat\mu_i(1 - \hat\mu_i)\}$, $\hat\Sigma = \hat W^{-1} + \hat\tau \Psi$ and

$$\hat P = \hat\Sigma^{-1} - \hat\Sigma^{-1} X (X^\top \hat\Sigma^{-1} X)^{-1} X^\top \hat\Sigma^{-1}.$$

With the covariate-adjusted genotype $\tilde G = G - X (X^\top \hat W X)^{-1} X^\top \hat W G$, the score statistic for $H_0 : \beta = 0$ is $T = \tilde G^\top (Y - \hat\mu)$ with variance $\operatorname{Var}(T) = \tilde G^\top \hat P \tilde G$. Let $\operatorname{Var}^*(T) = \tilde G^\top \hat W \tilde G$, the variance computed as if $\hat b$ were the true random effect, and $r = \operatorname{Var}(T) / \operatorname{Var}^*(T)$. SAIGE treats $r$ as constant across variants, estimates it as $\hat r$ from a small random set of variants (30 in the paper), and uses

$$T_{\mathrm{adj}} = \frac{\tilde G^\top (Y - \hat\mu)}{\sqrt{\hat r\, \tilde G^\top \hat W \tilde G}},$$

which has mean $0$ and variance approximately $1$ under $H_0$ and costs $O(N)$ per variant.

## Depends on

- [Mixed-model association chi-squared statistic](../../../proximal-contamination-in-mixed-model-associatio/mm-chi-sq.md)

## Expansion

Computing $\tilde G^\top \hat P \tilde G$ exactly needs a linear solve with $\hat\Sigma$ for every variant, whereas $\tilde G^\top \hat W \tilde G$ is a weighted sum of squares. The near-constancy of $r$ across variants is shown empirically in the paper's supplement (the same device is used by BOLT-LMM and GRAMMAR-Gamma). The null fit itself uses preconditioned conjugate gradients instead of inverting $\hat\Sigma$.

## Sources

- W. Zhou et al., *Efficiently controlling for case-control imbalance and sample relatedness in large-scale genetic association studies*, Nat. Genet. 50 (2018), 1335–1341. <https://doi.org/10.1038/s41588-018-0184-y> (PMCID: PMC6119127) Online Methods, "Generalized linear mixed model for binary traits" and "Estimate variance component and other model parameters (Step 1)".
