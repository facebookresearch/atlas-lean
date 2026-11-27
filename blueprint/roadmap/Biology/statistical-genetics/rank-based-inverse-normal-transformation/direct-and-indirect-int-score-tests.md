# Direct and indirect INT association tests

Let $y \in \mathbb{R}^n$ be a phenotype, $X$ an $n \times p$ full-rank covariate matrix (with intercept), $g \in \mathbb{R}^n$ a genotype, and $P_X = I - X(X^\top X)^{-1}X^\top$ the residual-forming projection. Let $\mathrm{INT}$ be the [rank-based inverse normal transformation](rank-based-inverse-normal-transformation.md), applied coordinatewise through ranks.

**Direct INT (D-INT).** Regress $z = \mathrm{INT}(y)$ on covariates and genotype, $z = X\beta_X + g\beta_G + \epsilon_D$, and test $H_0: \beta_G = 0$ with the score statistic

$$T_D = \frac{z^\top P_X g\,(g^\top P_X g)^{-1} g^\top P_X z}{\hat\sigma_D^2}, \qquad \hat\sigma_D^2 = \frac{z^\top P_X z}{n - p},$$

referred to $\chi^2_1$. It targets models $y = h(X\beta_X + g\beta_G + \epsilon)$ with $h$ rank preserving and normal $\epsilon$.

**Indirect INT (I-INT).** Transform the phenotypic residuals, $\tilde z = \mathrm{INT}(e_Y)$ with $e_Y = P_X y$, and regress on the genotypic residual $e_G = P_X g$: $\tilde z = e_G\beta_G + \epsilon_I$. The score statistic is

$$T_I = \frac{(e_G^\top\tilde z)^2}{(e_G^\top e_G)\,\sigma_I^2} = \frac{\tilde z^\top P_X g\,(g^\top P_X g)^{-1} g^\top P_X\tilde z}{\sigma_I^2},$$

referred to $\chi^2_1$. It targets models $y = X\beta_X + g\beta_G + \epsilon$ with arbitrary continuous residual law.

**Double adjustment adds nothing.** Because INT is nonlinear, $\tilde z$ is no longer orthogonal to the columns of $X$, and re-adjusting for covariates in $\tilde z = X\beta_X + g\beta_G + \epsilon_I$ has been recommended. The score statistic for $\beta_G$ in this doubly adjusted model has the same numerator $\tilde z^\top P_X g\,(g^\top P_X g)^{-1} g^\top P_X\tilde z$ as the I-INT statistic, so with the same residual-variance estimate the two tests coincide: adjusting the INT-transformed residuals for covariates again is equivalent to regressing them on the genotypic residual.

## Depends on

- [Rank-based inverse normal transformation](rank-based-inverse-normal-transformation.md)

## Expansion

The score statistic for $\beta_G$ in a Gaussian linear model $w = X\beta_X + g\beta_G + \epsilon$ at $\beta_G = 0$ is $(g^\top P_X w)^2/(g^\top P_X g\,\sigma^2)$, obtained by profiling out $\beta_X$. For the model with the single regressor $e_G$ and no covariates, the statistic is $(e_G^\top\tilde z)^2/(e_G^\top e_G\,\sigma^2)$, and $e_G^\top\tilde z = g^\top P_X\tilde z$, $e_G^\top e_G = g^\top P_X g$ because $P_X$ is symmetric and idempotent. D-INT is motivated by the approximation $\Phi^{-1}(F_{Y,n}(y_i)) \approx h^{-1}(y_i)/\sigma_D$, exact asymptotically under the complete null $\beta_X = 0$, $\beta_G = 0$; I-INT by the fact that, under $H_0: \beta_G = 0$, $\mathrm{INT}(e_Y)$ is asymptotically standard normal.

## Sources

- Z. R. McCaw, J. M. Lane, R. Saxena, S. Redline and X. Lin, "Operating characteristics of the rank-based inverse normal transformation for quantitative trait analysis in genome-wide association studies", Biometrics 76 (2020), <https://doi.org/10.1111/biom.13214> (PMC8643141); preprint version <https://doi.org/10.1101/635706>, sections 2.4–2.5, Equations (4)–(14).
