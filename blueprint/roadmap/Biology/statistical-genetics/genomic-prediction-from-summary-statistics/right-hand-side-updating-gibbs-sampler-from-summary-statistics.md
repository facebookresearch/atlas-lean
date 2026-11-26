# Right-hand-side updating Gibbs sampler from summary statistics

In the multiple-regression model $y = X\beta + \varepsilon$, $\varepsilon\sim N(0,\sigma_\varepsilon^2 I)$, take for illustration the two-component prior $\beta_j = 0$ or $\beta_j \sim N(0, \sigma_\beta^2)$. For a marker currently in the model, with $X_{-j}$ the genotype matrix without column $j$,

$$\beta_j \mid \theta_{-\beta_j}, y \sim N\!\left(\hat\beta_j,\; \sigma_\varepsilon^2/l_j\right), \qquad l_j = x_j^\top x_j + \sigma_\varepsilon^2/\sigma_\beta^2, \qquad \hat\beta_j = \frac{x_j^\top(y - X_{-j}\beta_{-j})}{l_j}.$$

**Right-hand-side identity.** Define the corrected right-hand side $r^* = X^\top y - X^\top X\beta \in \mathbb R^p$. Then

$$x_j^\top(y - X_{-j}\beta_{-j}) = r^*_j + x_j^\top x_j\,\beta_j,$$

and after $\beta_j$ is redrawn from $\beta_j^{(i)}$ to $\beta_j^{(i+1)}$,

$$r^{*(i+1)} = r^{*(i)} - X^\top x_j\,\bigl(\beta_j^{(i+1)} - \beta_j^{(i)}\bigr).$$

Consequently the whole sampler needs only $X^\top y = Db$ (from marginal estimates $b$ and $D = \operatorname{diag}(x_j^\top x_j)$) and the columns of $X^\top X = D^{1/2}BD^{1/2}$, never individual genotypes or phenotypes.

## Proof sketch

The full conditional follows by completing the square in $\beta_j$ in $-\frac{1}{2\sigma_\varepsilon^2}\|y - X_{-j}\beta_{-j} - x_j\beta_j\|^2 - \frac{\beta_j^2}{2\sigma_\beta^2}$. The identity holds because $r^*_j = x_j^\top y - x_j^\top X_{-j}\beta_{-j} - x_j^\top x_j\beta_j$, and the update subtracts the change in $X^\top X\beta$, which is $X^\top x_j$ times the change in $\beta_j$. Each update costs one sparse column of the LD matrix; in practice the reference LD matrix is shrunk entrywise by $\exp(-\varrho_{ij}/2m)$, with $\varrho_{ij} = 4N_e c_{ij}$ the population-scaled recombination rate between markers $i$ and $j$ and $m$ the size of the sample used to build the genetic map, and entries below a cutoff are set to zero to keep the columns sparse.

## Depends on

- [SBayesR: multiple-regression likelihood on summary statistics with a BayesR mixture prior](sbayesr-summary-statistic-likelihood-with-bayesr-mixture-prior.md)

## Sources

- L. R. Lloyd-Jones, J. Zeng, J. Sidorenko et al., "Improved polygenic prediction by Bayesian multiple regression on summary statistics", Nature Communications (2019), Methods ("SBayesR model overview", Equations 1–10, and "Reference LD matrix construction"), <https://doi.org/10.1038/s41467-019-12653-0> (PMC6841727).
