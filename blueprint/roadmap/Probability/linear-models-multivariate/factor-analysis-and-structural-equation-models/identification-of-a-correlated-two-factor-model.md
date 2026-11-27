# Identification of a correlated two-factor model

Consider the confirmatory two-factor model for $p = 5$ indicators in which factor $1$ loads only on items $1$–$3$ with nonzero loadings $\lambda_1, \lambda_2, \lambda_3$ and factor $2$ only on items $4$–$5$ with loadings $\lambda_4, \lambda_5$, the factors have unit variances and correlation $\varphi$, and the [covariance](correlated-two-factor-cov.md) is $\Sigma = \Lambda\Phi\Lambda^{\mathsf T} + \Psi$ with diagonal $\Psi \ge 0$. Fix the sign of factor $1$ by $\lambda_1 > 0$; then $\lambda_1, \lambda_2, \lambda_3$ are determined by $\Sigma$, as in the one-factor model, through $\lambda_1^2 = \sigma_{12}\sigma_{13}/\sigma_{23}$ and its analogues.

(a) If $\varphi \ne 0$ is known, then $\lambda_4 = \sigma_{14}/(\lambda_1\varphi)$ and $\lambda_5 = \sigma_{15}/(\lambda_1\varphi)$ are determined, zero values included, and so is $\Psi$.

(b) If $\varphi$ is unknown and $\varphi, \lambda_4, \lambda_5$ are all nonzero, then $\varphi^2 = \sigma_{14}\sigma_{15}/(\lambda_1^2\sigma_{45})$. Fixing the sign of $\lambda_4$ fixes the sign of $\varphi$ through $\sigma_{14}=\lambda_1\varphi\lambda_4$, after which (a) recovers the remaining parameters.

(c) If $\varphi$ is unknown, $\lambda_5 = 0$, $\lambda_4 \ne 0$ and $|\varphi| < 1$, the parameters are not identified: for every $t$ with $|\varphi| < t \le 1$, replacing $\varphi, \lambda_4$ and the fourth uniqueness $\psi_4$ by $\varphi/t$, $t\lambda_4$ and $\psi_4 + (1 - t^2)\lambda_4^2$ leaves $\Sigma$ unchanged. For $|\varphi|<t<1$, the fourth loading changes, so these are genuinely different parameters.

Proof. The cross-factor covariances are $\sigma_{jk} = \lambda_j\varphi\lambda_k$ for $j \le 3 < k$, and $\sigma_{45} = \lambda_4\lambda_5$. In (a) divide by the known $\lambda_1\varphi$. In (b), $\sigma_{14}\sigma_{15} = \lambda_1^2\varphi^2\lambda_4\lambda_5 = \lambda_1^2\varphi^2\sigma_{45}$ with $\sigma_{45} \ne 0$; then $\lambda_4 = \sigma_{14}/(\lambda_1\varphi)$, and similarly $\lambda_5$. In (c) the products $\varphi\lambda_4$, $\lambda_5$ and $\lambda_4^2 + \psi_4$ are unchanged, the new correlation lies in $(-1, 1)$, and the new uniqueness is nonnegative.

## Background

- [Positive degrees of freedom do not imply identification of a factor model](positive-degrees-of-freedom-do-not-imply-identification.md): the uncorrelated model, in which the loadings are not identified.
- [Identification of a one-factor model from three indicators](identification-of-the-one-factor-model.md): identification of the first factor's loadings.

## Sources

- D. A. Kenny, *Identification: Overview* (SEM web notes), 2011, Rule on number of indicators per latent variable (Condition B2a), <http://davidakenny.net/cm/identify.htm>. The source states a special case or part of the statement; the rest is derived on this page.
