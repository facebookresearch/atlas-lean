# EMMA spectral reduction of ML and REML to one variable

Let $y \in \mathbb{R}^n$ be phenotypes, $X \in \mathbb{R}^{n \times q}$ a full-column-rank fixed-effect design (intercept, tested marker, covariates), $Z \in \mathbb{R}^{n \times t}$ an incidence matrix mapping observations to $t$ strains, and $K \in \mathbb{R}^{t \times t}$ a symmetric positive semidefinite kinship matrix. Consider the linear mixed model

$$y = X\beta + Zu + e, \qquad u \sim N(0, \sigma_g^2 K), \qquad e \sim N(0, \sigma_e^2 I_n),$$

with $u$ and $e$ independent, so that $\operatorname{Var}(y) = \sigma_g^2 H_\delta$ with

$$H_\delta = ZKZ^\top + \delta I_n, \qquad \delta = \sigma_e^2/\sigma_g^2 > 0.$$

Let $S = I_n - X(X^\top X)^{-1}X^\top$. Take an eigendecomposition $ZKZ^\top = U_F \operatorname{diag}(\xi_1,\dots,\xi_n) U_F^\top$, and an $n \times (n-q)$ matrix $U_R$ with orthonormal columns spanning the range of $S$ such that $S\,ZKZ^\top S\,U_R = U_R \operatorname{diag}(\lambda_1,\dots,\lambda_{n-q})$. Both decompositions are computed once and do not depend on $\delta$; all $\xi_i, \lambda_s \ge 0$. Put $\eta = U_R^\top y$.

**Statement.** After maximizing over $\beta$ and $\sigma_g^2$, the full log-likelihood and the restricted log-likelihood are, as functions of $\delta > 0$ alone,

$$\ell_F(\delta) = \frac{n}{2}\log\frac{n}{2\pi} - \frac{n}{2} - \frac{n}{2}\log\sum_{s=1}^{n-q}\frac{\eta_s^2}{\lambda_s+\delta} - \frac12\sum_{i=1}^{n}\log(\xi_i+\delta),$$

$$\ell_R(\delta) = \frac{n-q}{2}\log\frac{n-q}{2\pi} - \frac{n-q}{2} - \frac{n-q}{2}\log\sum_{s=1}^{n-q}\frac{\eta_s^2}{\lambda_s+\delta} - \frac12\sum_{s=1}^{n-q}\log(\lambda_s+\delta),$$

the latter up to an additive constant that does not depend on $\delta$. The maximizing variance component is $\hat\sigma_g^2 = R(\delta)/n$ (ML) or $R(\delta)/(n-q)$ (REML) with $R(\delta) = \sum_s \eta_s^2/(\lambda_s+\delta)$, and

$$\frac{d\ell_R}{d\delta} = \frac{n-q}{2}\,\frac{\sum_s \eta_s^2/(\lambda_s+\delta)^2}{\sum_s \eta_s^2/(\lambda_s+\delta)} - \frac12\sum_{s=1}^{n-q}\frac{1}{\lambda_s+\delta}.$$

Each evaluation of $\ell_F$, $\ell_R$ or their derivatives costs $O(n)$ after the $O(n^3)$ decompositions, so the global optimum over $\delta$ can be located by a grid search combined with Newton–Raphson on the single parameter $\delta$.

## Depends on

- [GREML covariance matrix](../greml-and-haseman-elston-estimation-of-snp-herit/greml-cov.md)

## Proof depends on

- [Orthonormal error contrasts rotate to diagonalize a symmetric matrix](../greml-and-haseman-elston-estimation-of-snp-herit/exists-is-spectral-contrast.md)

## Expansion

The generalized residual sum of squares after profiling $\beta$ is $y^\top P y$ with $P = H_\delta^{-1} - H_\delta^{-1}X(X^\top H_\delta^{-1}X)^{-1}X^\top H_\delta^{-1}$. The classical identity $P = U_R (U_R^\top H_\delta U_R)^{-1} U_R^\top$ holds for any orthonormal basis $U_R$ of the orthogonal complement of the column space of $X$; since $U_R^\top H_\delta U_R = U_R^\top S H_\delta S U_R = \operatorname{diag}(\lambda_s + \delta)$, one gets $y^\top P y = \sum_s \eta_s^2/(\lambda_s+\delta)$. Also $\log\det H_\delta = \sum_i \log(\xi_i+\delta)$, and for REML $\log\det H_\delta + \log\det(X^\top H_\delta^{-1}X) - \log\det(X^\top X) = \log\det(U_R^\top H_\delta U_R) = \sum_s\log(\lambda_s+\delta)$. Substituting the profiled $\sigma_g^2$ gives both formulas.

## Sources

- H. M. Kang, N. A. Zaitlen, C. M. Wade, A. Kirby, D. Heckerman, M. J. Daly and E. Eskin, "Efficient control of population structure in model organism association mapping", Genetics 178 (2008), 1709–1723, Methods (EMMA), Equations (1)–(9), <https://doi.org/10.1534/genetics.107.080101> (PMC2278096).
