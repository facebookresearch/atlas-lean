# SBayesR: multiple-regression likelihood on summary statistics with a BayesR mixture prior

Let $y = X\beta + \varepsilon$ with $y \in \mathbb R^n$ centred, $X$ an $n\times p$ genotype matrix with centred (or scaled) columns $x_j$, and $\varepsilon \sim N(0, \sigma_\varepsilon^2 I_n)$. Let $D = \operatorname{diag}(x_1^\top x_1,\dots,x_p^\top x_p)$ (assumed positive), $b = D^{-1}X^\top y$ the vector of marginal least-squares estimates and $B = D^{-1/2}X^\top X D^{-1/2}$ the LD correlation matrix.

**Summary-statistic likelihood.** Multiplying the regression by $D^{-1}X^\top$ gives $b = D^{-1/2}BD^{1/2}\beta + D^{-1}X^\top\varepsilon$, hence

$$b \mid \beta \sim N\!\left(D^{-1/2}BD^{1/2}\beta,\; D^{-1/2}BD^{-1/2}\sigma_\varepsilon^2\right).$$

Without individual data, $B$ is replaced by a reference-panel estimate $\hat B$ and $D$ by $\hat D = \operatorname{diag}\{1/[\hat\sigma^2(b_j) + b_j^2/n_j]\}$, built from each marginal estimate $b_j$, its standard error $\hat\sigma(b_j)$ and its sample size $n_j$ (for standardized genotypes, $\hat D = \operatorname{diag}(n_1,\dots,n_p)$).

**BayesR prior.** Independently over markers,

$$\beta_j \mid \pi, \sigma_\beta^2 \sim \sum_{c=1}^{C}\pi_c\, N(0, \gamma_c\sigma_\beta^2), \qquad \gamma_1 = 0,$$

a finite mixture with a point mass at zero and prespecified variance multipliers (default $\gamma = (0, 0.01, 0.1, 1)$), with scaled inverse-$\chi^2$ priors on $\sigma_\beta^2$ and $\sigma_\varepsilon^2$. Inference targets $p(\beta \mid b, D, B) \propto p(b \mid \beta, D, B)\,p(\beta)$ by Gibbs sampling; SNP heritability is tracked as $h^2_{\mathrm{SNP}} = \sigma_g^2/(\sigma_g^2 + \sigma_\varepsilon^2)$ with $\sigma_g^2$ the sample variance of $X\beta$ at each iteration.

## Remarks

The likelihood is exact under the individual-level model: $D^{-1}X^\top X = D^{-1/2}BD^{1/2}$ and $\operatorname{Var}(D^{-1}X^\top\varepsilon) = \sigma_\varepsilon^2 D^{-1}X^\top X D^{-1} = \sigma_\varepsilon^2 D^{-1/2}BD^{-1/2}$. The reconstruction of $\hat D$ uses that, for a centred marker, the residual variance of the simple regression is about $x_j^\top x_j\,\hat\sigma^2(b_j)$ and the phenotypic variance about $x_j^\top x_j(\hat\sigma^2(b_j) + b_j^2/n_j)$, which is one after standardizing the phenotype. The mixture prior lets most markers have zero effect while a few carry large effects, a sparser and heavier-tailed architecture than the single normal prior of summary-statistic BLUP.

## Depends on

- [Marginal least-squares estimate of a marker effect](marginal-estimate.md)
- [In-sample LD matrix](ld-matrix.md)

## Sources

- L. R. Lloyd-Jones, J. Zeng, J. Sidorenko et al., "Improved polygenic prediction by Bayesian multiple regression on summary statistics", Nature Communications (2019), Methods ("SBayesR model overview", Equations 1–10, and "Reference LD matrix construction"), <https://doi.org/10.1038/s41467-019-12653-0> (PMC6841727).
