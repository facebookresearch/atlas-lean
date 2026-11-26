# Mediation decomposition in summary-data Mendelian randomization

Let $X$ be a risk factor, $M$ a mediator and $Y$ an outcome, related linearly and without effect modification by causal effects $\theta_1$ ($X \to M$), $\theta_2$ ($X \to Y$ not via $M$) and $\theta_3$ ($M \to Y$). The direct effect of $X$ on $Y$ is $\theta_D = \theta_2$, the indirect effect via $M$ is $\theta_I = \theta_1\theta_3$, and the total effect is $\theta_T = \theta_D + \theta_I = \theta_2 + \theta_1\theta_3$.

Let $G_1, \dots, G_J$ be uncorrelated genetic variants with summarized associations $\hat\beta_{Xj}$, $\hat\beta_{Mj}$, $\hat\beta_{Yj}$ and outcome standard errors $\operatorname{se}(\hat\beta_{Yj})$. The two estimators are weighted least-squares regressions through the origin, with weights $\operatorname{se}(\hat\beta_{Yj})^{-2}$:

$$\hat\beta_{Yj} = \theta_T \hat\beta_{Xj} + \epsilon_{Tj}, \qquad \hat\beta_{Yj} = \theta_D \hat\beta_{Xj} + \theta_M \hat\beta_{Mj} + \epsilon_{Dj}.$$

The first is the [inverse-variance-weighted estimator](ivw.md) of $\theta_T$ and is consistent when every variant is a valid instrument for $X$. The second is multivariable Mendelian randomization and is consistent for $\theta_D$ (with $\theta_M = \theta_3$) when every variant is associated with $X$ or $M$, is independent of confounders, and affects $Y$ only through $X$ and $M$. The indirect effect is estimated by $\hat\theta_T - \hat\theta_D$, and a difference between total and direct effects indicates that part of the causal pathway passes through $M$.

The direct effect is identified only if the vectors $(\beta_{Xj})_j$ and $(\beta_{Mj})_j$ are not proportional. If every variant affects $M$ only through $X$ with a common effect, then $\beta_{Mj} = \theta_1 \beta_{Xj}$ for all $j$, the two regressors are collinear, and $\theta_D$ is not identified even with infinite sample size. Heterogeneity in the $X \to M$ effect across variants, $M_i = \alpha_0 + (\alpha_X + \sum_j \psi_j g_{ij}) X_i + \eta_i$ with zero-mean $\psi_j$, restores identification of $\theta_D$; it attenuates but does not invalidate inference on $\theta_T$.

## Remarks

Under the linear model the true associations satisfy $\beta_{Mj} = \theta_1\beta_{Xj}$ (plus any variant-specific deviation) and $\beta_{Yj} = \theta_2\beta_{Xj} + \theta_3\beta_{Mj}$. Substituting the first into the second gives $\beta_{Yj} = (\theta_2 + \theta_1\theta_3)\beta_{Xj} = \theta_T\beta_{Xj}$, so the univariable regression recovers $\theta_T$. The multivariable regression solves the normal equations in the two regressors and recovers $(\theta_2, \theta_3)$ whenever the weighted Gram matrix of $(\hat\beta_{Xj}, \hat\beta_{Mj})$ is nonsingular, which fails exactly in the proportional case. The weighted regression with outcome-scale weights is the summary-data form of two-stage least squares.

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)

## Sources

- S. Burgess, D. J. Thompson, J. M. B. Rees, F. R. Day, J. R. Perry and K. K. Ong, Dissecting causal pathways using Mendelian randomization with summarized genetic data: application to age at menarche and risk of breast cancer, *Genetics* 207 (2017), 481–487, <https://doi.org/10.1534/genetics.117.300191>, PMCID PMC5629317 (Methods, Equations 1–4 and Figure 2).
