# SEF moment-matching test for differential expression densities

**Setting.** In population-scale single-cell RNA-seq, individual $i$ in group $t \in \{t_1, t_2\}$ contributes $m_i$ cells whose expression values $y$ of a gene are draws from an individual density $f^{(t)}_i$; the $f^{(t)}_i$ are i.i.d. random densities from a law $\mathcal{D}_t$, with group mean density $f^{(t)}$. Let $r_{1}, r_{2}$ be the limiting cell proportions of the two groups and $t(y) = (t_1(y), \dots, t_p(y))$ chosen sufficient statistics (e.g. $y, y^2, \dots, y^p$).

**Specially designed exponential family (SEF).** Each density is modelled as an exponential tilt of a common carrier, $f_\beta(y) = \hat\mu_0(y) \exp(t(y)^\top \beta)$, where $\hat\mu_0$ is a kernel density estimate of the pooled data and $\beta$ (including an intercept) is fitted by moment matching, $\int t(y) f_\beta(y)\,dy = $ the empirical mean of $t$. Binning $y$ into $K$ bins with counts $s_k$, this is a Poisson regression $s_k \sim \mathrm{Poisson}\big(m |\mathcal{Y}_k| \hat\mu_0(y_{(k)}) e^{t(y_{(k)})^\top \beta}\big)$, solved by $X^\top[\mathbf{s} - m\,\hat{\boldsymbol\mu}_0 \odot e^{X\hat\beta} |\mathcal{Y}_K|] = 0$ with design rows $(1, y_{(k)}, \dots, y_{(k)}^p)$. Fitting per individual gives $\hat\beta^{t,i}$; fitting each group's pooled cells gives $\hat\beta^{t_1}, \hat\beta^{t_2}$.

**Proposition (what is estimated).** Under the random-density model and finite second moments of $t$, the group-level SEF estimators asymptotically solve

$$
\int t(y)\, \big(r_1 f^{(t_1)} + r_2 f^{(t_2)}\big)(y)\, e^{t(y)^\top \beta^{t_l}}\, dy = \int t(y) f^{(t_l)}(y)\, dy, \qquad l = 1, 2,
$$

so $\beta^{t_l}$ tilts the pooled density to match the $t$-moments of group $t_l$. Hence, with $r_1 + r_2 = 1$, $\int t f^{(t_1)} = \int t f^{(t_2)}$ iff $\beta^{t_1} = \beta^{t_2} = 0$, and testing equality of the two expression densities in the $t$-moments is equivalent to testing $H_0 : \beta^{t_1} - \beta^{t_2} = 0$.

**Theorem (sandwich covariance and Wald test).** With $G_{t_l} = X^\top D(\hat{\boldsymbol\mu}_0 \odot e^{X\hat\beta^{t_l}} |\mathcal{Y}_k|) X$ and weight matrices $Z_{t_l, j}^\top = X^\top\big\{\frac{\mathbf{1}\{j \in T_l\}}{\sum_{i \in T_l} m_i} I_K - D(e^{X\hat\beta^{t_l}} |\mathcal{Y}_k|)\, d\hat{\boldsymbol\mu}_0/d\mathbf{s}_j\big\}$ (accounting for the dependence of the KDE carrier on every individual's counts $\mathbf{s}_j$),

$$
\hat\Sigma_{\hat\beta^{t_1} - \hat\beta^{t_2}} = \sum_{j=1}^n \big(G_{t_1}^{-1} Z_{t_1,j}^\top - G_{t_2}^{-1} Z_{t_2,j}^\top\big)\, \widehat{\mathrm{Cov}}(\mathbf{s}_j)\, \big(G_{t_1}^{-1} Z_{t_1,j}^\top - G_{t_2}^{-1} Z_{t_2,j}^\top\big)^\top,
$$

with analogous formulas for individual- and group-level estimates, and a consistent estimator of the covariance. The joint Wald statistic $(\hat\beta^{t_1} - \hat\beta^{t_2})^\top \hat\Sigma^{-1} (\hat\beta^{t_1} - \hat\beta^{t_2})$ is referred to $\chi^2_{p+1}$; since the non-intercept part $\beta_1 \in \mathbb{R}^p$ already determines the distribution, a marginal Wald test on it is also used.

## Expansion

Treating individuals, not cells, as the replication unit is what makes the covariance valid: $\widehat{\mathrm{Cov}}(\mathbf{s}_j)$ is estimated across individuals, capturing the between-individual variability of the random densities $f^{(t)}_i$, and the delta method through the estimating equation and the KDE carrier yields the sandwich form. Compared with parametric Poisson–Gamma or zero-inflated negative binomial models, the SEF avoids specifying the shape of the expression distribution, and choosing $t$ targets the moments of interest (mean, variance, skewness).

## Sources

- H. Ye, Z. Qian, H. Li, "Differential Density Analysis in Single-Cell Genomics Using Specially Designed Exponential Families", arXiv:2510.24948 (2025): Section 2 (SEF model, Poisson-regression estimating equations, Assumptions 1–3), Proposition 2 (moment matching to the pooled density and the equivalent null hypothesis), Theorem 2 and Corollary 2 (approximate covariance of SEF estimates), Section on test statistics (joint and marginal Wald tests). <https://doi.org/10.48550/arXiv.2510.24948>
