# Delta-method and Fieller intervals for the instrumental-variable ratio estimate

Let $\hat\beta_{Y|Z}$ and $\hat\beta_{X|Z}$ be the estimated associations of a single instrument $Z$ with the outcome $Y$ and the exposure $X$, jointly approximately normal with means $\beta_{Y|Z}, \beta_{X|Z}$, variances $v_{YY} = \mathrm{se}(\hat\beta_{Y|Z})^2$, $v_{XX} = \mathrm{se}(\hat\beta_{X|Z})^2$ and covariance $v_{XY}$. The causal effect is the ratio $\theta = \beta_{Y|Z}/\beta_{X|Z}$ (assuming $\beta_{X|Z} \neq 0$) and $\hat\theta = \hat\beta_{Y|Z}/\hat\beta_{X|Z}$ is the ratio estimate.

**Delta method (Eq. 4).** To first order,

$$\mathrm{se}(\hat\theta)^2 \approx \frac{v_{YY}}{\hat\beta_{X|Z}^2} + \frac{\hat\beta_{Y|Z}^2\, v_{XX}}{\hat\beta_{X|Z}^4} - \frac{2\hat\beta_{Y|Z}\, v_{XY}}{\hat\beta_{X|Z}^3},$$

and the last term vanishes when the two associations come from independent samples.

**Fieller's theorem.** For every fixed $\theta$ the pivot $\hat\beta_{Y|Z} - \theta\hat\beta_{X|Z}$ is normal with mean $0$ and variance $v_{YY} - 2\theta v_{XY} + \theta^2 v_{XX}$. Hence, with $z = z_{1-\alpha/2}$, the set

$$\mathcal C = \bigl\{\theta \in \mathbb R : (\hat\beta_{Y|Z} - \theta\hat\beta_{X|Z})^2 \le z^2 (v_{YY} - 2\theta v_{XY} + \theta^2 v_{XX})\bigr\}$$

has exact coverage $1 - \alpha$ under the normal model. It is the solution set of the quadratic inequality $A\theta^2 - 2B\theta + D \le 0$ with $A = \hat\beta_{X|Z}^2 - z^2 v_{XX}$, $B = \hat\beta_{Y|Z}\hat\beta_{X|Z} - z^2 v_{XY}$, $D = \hat\beta_{Y|Z}^2 - z^2 v_{YY}$. So $\mathcal C$ is:

- a bounded interval $[\,(B - \sqrt{B^2 - AD})/A,\ (B + \sqrt{B^2 - AD})/A\,]$ if $A > 0$, i.e. the instrument–exposure association is significant at level $\alpha$;
- the complement of a bounded interval (two half-lines) if $A < 0$ and $B^2 - AD > 0$;
- the whole real line if $A < 0$ and $B^2 - AD \le 0$.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Ratio of independent normal variables is not integrable](not-integrable-div-gaussian.md)

## Expansion

The delta formula is the gradient $(1/\beta_{X|Z}, -\beta_{Y|Z}/\beta_{X|Z}^2)$ of $(\beta_Y, \beta_X) \mapsto \beta_Y/\beta_X$ applied to the covariance matrix of the two estimates. Since the ratio estimator has no finite mean, Wald intervals built on this standard error are too narrow when $\hat\beta_{X|Z}$ is close to zero relative to its standard error, i.e. for a weak instrument. Fieller's construction avoids the ratio's distribution altogether. It inverts the exact normal test of $H_0: \beta_{Y|Z} - \theta\beta_{X|Z} = 0$ for each $\theta$. The test statistic is a quadratic in $\theta$, and the sign of its leading coefficient $A$ separates the three shapes. An unbounded set is the honest answer when the data cannot exclude $\beta_{X|Z} = 0$. Bootstrap, Anderson–Rubin and conditional likelihood ratio intervals give alternatives, and the last two extend to several instruments.

## Sources

- S. Burgess, D. S. Small and S. G. Thompson, "A review of instrumental variable estimators for Mendelian randomization", Statistical Methods in Medical Research (2015 online; 2017), Sections 3.4.1–3.4.4 (Equation (4)) and 3.5, <https://doi.org/10.1177/0962280215597579>, PMCID PMC5642006.
