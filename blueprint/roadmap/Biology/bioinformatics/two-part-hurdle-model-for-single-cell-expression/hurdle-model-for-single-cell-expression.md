# Two-part hurdle model for single-cell expression

Let $y_{ig} \ge 0$ be a normalized expression value (for example $\log_2(\mathrm{TPM}+1)$) of gene $g \in \{1,\dots,N\}$ in cell $i \in \{1,\dots,n\}$, and let $z_{ig} = \mathbf{1}\{y_{ig} > 0\}$ be its detection indicator. Let $X_i \in \mathbb{R}^{1 \times p}$ be the covariate row of cell $i$. The two-part hurdle model assumes that, for each gene $g$, the detection indicator and the positive expression level are conditionally independent given $X_i$ and are modelled by

$$\operatorname{logit}\big(\Pr(Z_{ig} = 1)\big) = X_i \beta^D_g, \qquad \big(Y_{ig} \mid Z_{ig} = 1\big) \sim \mathcal{N}\big(X_i \beta^C_g, \ \sigma_g^2\big),$$

with discrete coefficients $\beta^D_g \in \mathbb{R}^p$, continuous coefficients $\beta^C_g \in \mathbb{R}^p$ and variance $\sigma_g^2 > 0$. The unconditional density of $Y_{ig}$ with respect to the sum of Lebesgue measure on $(0,\infty)$ and a point mass at $0$ is therefore

$$f(y) = \big(1 - \pi_{ig}\big)\,\mathbf{1}\{y = 0\} + \pi_{ig}\,\varphi\!\left(\frac{y - X_i\beta^C_g}{\sigma_g}\right)\frac{1}{\sigma_g}\,\mathbf{1}\{y > 0\}, \qquad \pi_{ig} = \frac{\exp(X_i\beta^D_g)}{1 + \exp(X_i\beta^D_g)},$$

where $\varphi$ is the standard normal density. Consequently $\mathbb{E}[Y_{ig} \mid X_i] = \pi_{ig}\, X_i \beta^C_g$: a covariate acts on the expected expression both through the detection rate and through the conditional mean.

## Depends on

- [Cellular detection rate](cellular-detection-rate.md)

## Expansion

Single-cell expression is bimodal: a gene is either undetected or expressed at a substantially non-zero level, so a single Gaussian or count likelihood misstates both components. The hurdle construction splits the sample space at the "hurdle" $y = 0$ and places a generalized linear model on each part, which keeps the full apparatus of design matrices (treatment, batch, nuisance covariates) available for both. Conditional independence of $Z_g$ and $(Y_g \mid Z_g = 1)$ given the covariates is what makes the joint log-likelihood separate into a logistic term and a Gaussian term, so the two components can be fitted independently gene by gene, and their test statistics recombined afterwards.

## Sources

- Finak G, McDavid A, Yajima M, et al. MAST: a flexible statistical framework for assessing transcriptional changes and characterizing heterogeneity in single-cell RNA sequencing data. *Genome Biology* 16:278 (2015), Methods, "Single-cell RNA-seq hurdle model". DOI <https://doi.org/10.1186/s13059-015-0844-5>. PMCID PMC4676162.
