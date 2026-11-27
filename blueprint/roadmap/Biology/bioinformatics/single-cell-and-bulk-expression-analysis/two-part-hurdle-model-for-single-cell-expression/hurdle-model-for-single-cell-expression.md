# Two-part hurdle model for single-cell expression

Let $y_{ig} \ge 0$ be a normalized expression value (for example $\log_2(\mathrm{TPM}+1)$) of gene $g \in \{1,\dots,N\}$ in cell $i \in \{1,\dots,n\}$, and let $z_{ig} = \mathbf{1}\{y_{ig} > 0\}$ be its detection indicator. Let $X_i \in \mathbb{R}^{1 \times p}$ be the covariate row of cell $i$, which includes the [cellular detection rate](cellular-detection-rate.md). For each gene $g$ the two-part hurdle model fits two regressions on the same design:

1. **Discrete part.** A logistic regression for detection over all cells,

$$\operatorname{logit}\big(\Pr(Z_{ig} = 1 \mid X_i)\big) = X_i \beta^D_g .$$

2. **Continuous part.** A Gaussian linear working regression fitted to the detected observations only, those with $z_{ig} = 1$,

$$y_{ig} = X_i \beta^C_g + \varepsilon_{ig}, \qquad \varepsilon_{ig} \sim \mathcal{N}(0, \sigma_g^2),$$

with discrete coefficients $\beta^D_g \in \mathbb{R}^p$, continuous coefficients $\beta^C_g \in \mathbb{R}^p$ and variance $\sigma_g^2 > 0$.

The two parts share no parameters, and the model treats the detection indicator and the positive expression level as conditionally independent given $X_i$, so the log-likelihood of the gene is the sum of a logistic term over all cells and a Gaussian term over the detected cells, and the two parts are estimated separately. The Gaussian part is a working model for the detected values: it puts mass on $(-\infty, 0]$, so the model does not define a normalized density for $Y_{ig}$ on $[0, \infty)$, and no formula for $\mathbb{E}[Y_{ig} \mid X_i]$ follows from it. A covariate can act on expression through the detection rate, through the level of the detected values, or both.

## Depends on

- [Cellular detection rate](cellular-detection-rate.md)

## Remarks

Single-cell expression is bimodal: a gene is either undetected or expressed at a substantially non-zero level, so a single Gaussian or count likelihood misstates both components. The hurdle construction splits the data at the "hurdle" $y = 0$ and places a generalized linear model on each part, which keeps the full apparatus of design matrices (treatment, batch, nuisance covariates) available for both. Because the parts share no parameters, they can be fitted independently gene by gene, and their test statistics recombined afterwards. A model with a proper density on $[0, \infty)$, for example a normal distribution truncated to $(0, \infty)$ for the detected values, would have a different conditional mean and is not what the source fits.

## Sources

- Finak G, McDavid A, Yajima M, et al. MAST: a flexible statistical framework for assessing transcriptional changes and characterizing heterogeneity in single-cell RNA sequencing data. *Genome Biology* 16:278 (2015), Methods, "Single-cell RNA-seq hurdle model". DOI <https://doi.org/10.1186/s13059-015-0844-5>. PMCID PMC4676162.
