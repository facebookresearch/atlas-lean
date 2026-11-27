# VBQTL joint model of genetic, known and hidden factors

Let $Y = (y_{g,j})$ be expression levels of genes $g = 1, \dots, G$ in individuals $j = 1, \dots, J$, with genotypes $s_{n,j}$ at SNPs $n = 1, \dots, N$ and known covariates $f_{c,j}$, $c = 1, \dots, C$. VBQTL models

$$y_{g,j} \mid y^{(1)}_{g,j}, y^{(2)}_{g,j}, y^{(3)}_{g,j}, \tau_g \sim N\bigl(y^{(1)}_{g,j} + y^{(2)}_{g,j} + y^{(3)}_{g,j},\ \tau_g^{-1}\bigr), \qquad \tau_g \sim \mathrm{Gamma}(a_\tau, b_\tau),$$

where each component $y^{(i)}_{g,j}$ is itself Gaussian with precision $\tau_g$ around a linear predictor:

1. **genotype:** mean $\sum_{n=1}^{N} b_{n,g}\,\theta_{n,g}\, s_{n,j}$, with $b_{n,g} \sim \mathrm{Bernoulli}(p_{\mathrm{ass}})$ indicating an association and effect $\theta_{n,g} \sim N(0, 1)$;
2. **known factors:** mean $\sum_{c=1}^{C} v_{g,c} f_{c,j}$, with $v_{g,c} \sim N(0, \alpha_c^{-1})$ and $\alpha_c \sim \mathrm{Gamma}(a_\alpha, b_\alpha)$;
3. **hidden factors:** mean $\sum_{k=1}^{K} w_{g,k} x_{k,j}$, with $x_{k,j} \sim N(0, 1)$, $w_{g,k} \sim N(0, \beta_k^{-1})$ and $\beta_k \sim \mathrm{Gamma}(a_\beta, b_\beta)$.

The gamma priors on the per-factor precisions $\alpha_c$, $\beta_k$ implement automatic relevance determination: a factor whose weights are all small acquires a large precision and is switched off, so $K$ need only be an upper bound. The prior association probability $p_{\mathrm{ass}}$ plays the role of a significance threshold. Inference is by variational Bayes on a factorized posterior; for tractability at most one SNP per gene is allowed to have $b_{n,g} = 1$.

## Expansion

Conditionally on all other variables, each weight vector, factor, effect and precision has a conjugate Gaussian or gamma conditional, which is what makes coordinate-wise variational updates closed-form. The model contains as special cases standard single-SNP regression (no factors), regression with known covariates, and Bayesian factor analysis without genetics (the hidden-factor component alone).

## Sources

- O. Stegle, L. Parts, R. Durbin and J. Winn, "A Bayesian framework to account for complex non-genetic factors in gene expression levels greatly increases power in eQTL studies", *PLoS Computational Biology* 6 (2010), e1000770, <https://doi.org/10.1371/journal.pcbi.1000770> (PMC2865505). Methods, equations (1)–(11) and Figure 2a.
