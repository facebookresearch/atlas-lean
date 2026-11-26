# Delta-method and Fieller intervals for the instrumental-variable ratio estimate

Let $\hat\beta_{Y|Z}$ and $\hat\beta_{X|Z}$ be the estimated associations of a single instrument $Z$ with the outcome $Y$ and the exposure $X$, jointly (approximately) normal with means $\beta_{Y|Z}, \beta_{X|Z}$, variances $v_{YY} = \mathrm{se}(\hat\beta_{Y|Z})^2$, $v_{XX} = \mathrm{se}(\hat\beta_{X|Z})^2$ and covariance $v_{XY}$. The causal effect is the ratio $\theta = \beta_{Y|Z}/\beta_{X|Z}$ (assuming $\beta_{X|Z} \neq 0$) and $\hat\theta = \hat\beta_{Y|Z}/\hat\beta_{X|Z}$ is the ratio estimate.

**Delta method (Eq. 4).** To first order,

$$\mathrm{se}(\hat\theta)^2 \approx \frac{v_{YY}}{\hat\beta_{X|Z}^2} + \frac{\hat\beta_{Y|Z}^2\, v_{XX}}{\hat\beta_{X|Z}^4} - \frac{2\hat\beta_{Y|Z}\, v_{XY}}{\hat\beta_{X|Z}^3},$$

and the last term vanishes when the two associations come from independent samples.

**Fieller's interval.** With $z = z_{1-\alpha/2}$, Fieller's set is [Fieller's confidence set](../../../Probability/not-yet-classified/part-17/fieller-ratio/fieller-set.md) with $a = \hat\beta_{Y|Z}$, $b = \hat\beta_{X|Z}$, $v_{aa} = v_{YY}$, $v_{bb} = v_{XX}$, $v_{ab} = v_{XY}$:

$$\mathcal C = \bigl\{\theta \in \mathbb R : (\hat\beta_{Y|Z} - \theta\hat\beta_{X|Z})^2 \le z^2 (v_{YY} - 2\theta v_{XY} + \theta^2 v_{XX})\bigr\}.$$

It inverts, for each candidate $\theta$, the test of $H_0(\theta) : \beta_{Y|Z} - \theta\beta_{X|Z} = 0$ based on $\hat\beta_{Y|Z} - \theta\hat\beta_{X|Z}$, whose mean $\beta_{Y|Z} - \theta\beta_{X|Z}$ is zero only under $H_0(\theta)$. If the two estimates are jointly Gaussian with the stated means and known variances and covariance, and $v_{YY} - 2\theta v_{XY} + \theta^2 v_{XX} > 0$ at the true ratio $\theta$, then $\mathcal C$ contains the true $\theta$ with probability exactly $1 - \alpha$ ([exact coverage of Fieller's set](../../../Probability/not-yet-classified/part-17/fieller-ratio/measure-real-mem-fieller-set.md)); when the estimates are only approximately normal, or their variances are estimated, the coverage is approximately $1 - \alpha$.

**Shape.** $\mathcal C$ is the solution set of $A\theta^2 - 2B\theta + D \le 0$ with $A = \hat\beta_{X|Z}^2 - z^2 v_{XX}$, $B = \hat\beta_{Y|Z}\hat\beta_{X|Z} - z^2 v_{XY}$, $D = \hat\beta_{Y|Z}^2 - z^2 v_{YY}$, and for a positive semidefinite covariance:

- if $A > 0$ (the instrument–exposure association is significant at level $\alpha$), a bounded closed interval $[\,(B - \sqrt{B^2 - AD})/A,\ (B + \sqrt{B^2 - AD})/A\,]$ containing $\hat\theta$;
- if $A < 0$, the complement of a bounded open interval (two half-lines) when $B^2 - AD > 0$, and the whole real line when $B^2 - AD \le 0$ ([shape of Fieller's set](../../../Probability/not-yet-classified/part-17/fieller-ratio/fieller-set-shape.md));
- if $A = 0$, the solution set of the linear inequality $-2B\theta + D \le 0$: the half-line $[D/(2B), \infty)$ if $B > 0$, the half-line $(-\infty, D/(2B)]$ if $B < 0$, and, if $B = 0$, the whole line when $D \le 0$ and the empty set when $D > 0$ (which for a positive semidefinite covariance requires $\hat\beta_{X|Z} = 0$ and $v_{XX} = 0$).

## Proof sketch

The delta formula is the gradient $(1/\beta_{X|Z}, -\beta_{Y|Z}/\beta_{X|Z}^2)$ of $(\beta_Y, \beta_X) \mapsto \beta_Y/\beta_X$ applied to the covariance matrix of the two estimates. Wald intervals built on this standard error are too narrow when $\hat\beta_{X|Z}$ is close to zero relative to its standard error, i.e. for a weak instrument, because the first-order expansion ignores the mass of $\hat\beta_{X|Z}$ near zero. When the two estimates are independent normals with $v_{XX} > 0$ and the outcome estimate is nondegenerate ($\beta_{Y|Z} \ne 0$ or $v_{YY} > 0$), the ratio estimator even has no finite mean ([the ratio of independent normal variables is not integrable](not-integrable-div-gaussian.md)); this does not follow for every positive semidefinite covariance allowed here, since with $v_{XX} = 0$ and $\beta_{X|Z} \ne 0$ the denominator is constant and the ratio is normal with finite mean. Fieller's construction avoids the ratio's distribution altogether. At the true ratio the pivot $(\hat\beta_{Y|Z} - \theta\hat\beta_{X|Z})^2/(v_{YY} - 2\theta v_{XY} + \theta^2 v_{XX})$ is $\chi^2_1$ under joint normality, which gives the coverage. The test statistic is a quadratic in $\theta$, and the sign of its leading coefficient $A$ separates the shapes; at $A = 0$ the quadratic term vanishes and the inequality is linear. An unbounded set is the honest answer when the data cannot exclude $\beta_{X|Z} = 0$. Bootstrap, Anderson–Rubin and conditional likelihood ratio intervals give alternatives, and the last two extend to several instruments.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Fieller's confidence set](../../../Probability/not-yet-classified/part-17/fieller-ratio/fieller-set.md)

## Proof depends on

- [Exact coverage of Fieller's set](../../../Probability/not-yet-classified/part-17/fieller-ratio/measure-real-mem-fieller-set.md)
- [Shape of Fieller's set](../../../Probability/not-yet-classified/part-17/fieller-ratio/fieller-set-shape.md)
- [Ratio of independent normal variables is not integrable](not-integrable-div-gaussian.md)

## Sources

- S. Burgess, D. S. Small and S. G. Thompson, "A review of instrumental variable estimators for Mendelian randomization", Statistical Methods in Medical Research (2015 online; 2017), Sections 3.4.1–3.4.4 (Equation (4)) and 3.5, <https://doi.org/10.1177/0962280215597579>, PMCID PMC5642006.
