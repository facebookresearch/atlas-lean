# Principal-component IVW estimator for many correlated instruments

Let $J$ genetic variants from one gene region have summarized associations $\hat\beta_{Xj}$ with a risk factor and $\hat\beta_{Yj}$ with an outcome, outcome standard errors $\sigma_{Yj} = \operatorname{se}(\hat\beta_{Yj})$, and pairwise correlations $\rho_{j_1 j_2}$ ($\rho_{jj} = 1$). Write $\hat\beta_X, \hat\beta_Y \in \mathbb{R}^J$ and $\Omega_{j_1 j_2} = \sigma_{Yj_1}\sigma_{Yj_2}\rho_{j_1 j_2}$.

**Correlated-variant IVW.** When $\Omega$ is invertible, generalized weighted least squares of $\hat\beta_Y$ on $\hat\beta_X$ through the origin gives

$$\hat\theta_{\mathrm{IVW}} = \big(\hat\beta_X^{\top}\Omega^{-1}\hat\beta_X\big)^{-1}\hat\beta_X^{\top}\Omega^{-1}\hat\beta_Y .$$

With individual-level data on centred instruments $Z \in \mathbb{R}^{N\times J}$ (with $H = Z^{\top}Z$ invertible and $D = \operatorname{diag}(H)$), exposure $X$ and outcome $Y$, take the univariable (marginal) slopes from that sample, $\hat\beta_X = D^{-1}Z^{\top}X$ and $\hat\beta_Y = D^{-1}Z^{\top}Y$, and take $\Omega$ on a common error scale, $\Omega = \sigma^2 D^{-1}HD^{-1}$ (that is, $\sigma_{Yj} = \sigma/\sqrt{H_{jj}}$ and $\rho$ the in-sample correlation of the instruments). Then $\hat\theta_{\mathrm{IVW}}$ equals the two-stage least squares estimate $\hat\theta_{\mathrm{2SLS}} = [X^{\top}Z(Z^{\top}Z)^{-1}Z^{\top}X]^{-1}X^{\top}Z(Z^{\top}Z)^{-1}Z^{\top}Y$. Same-sample estimates alone do not guarantee this: separately estimated marginal residual standard errors need not share the common scale $\sigma$, and then the equality is only approximate. If $\Omega$ is near-singular (variants in near-perfect linkage disequilibrium), entries of $\Omega^{-1}$ are huge and small discrepancies in the inputs (rounding, correlations estimated in another sample) produce overprecise and misleading estimates.

**Weighted PCA.** Form the weighted correlation matrix

$$\Psi_{j_1 j_2} = \frac{\hat\beta_{Xj_1}\hat\beta_{Xj_2}}{\sigma_{Yj_1}\sigma_{Yj_2}}\,\rho_{j_1 j_2},$$

whose diagonal entries $\hat\beta_{Xj}^2/\sigma_{Yj}^2$ are the inverse-variance weights (the precision of the single-variant ratio estimate). Take its eigendecomposition $\Psi = W\Lambda W^{\top}$ with eigenvalues $\lambda_1 > \dots > \lambda_J$, let $W_k$ be the first $k$ columns of $W$ ($k$ chosen so that the retained eigenvalues explain a set fraction, e.g. 99%, of the total), and set

$$\tilde\beta_X = W_k^{\top}\hat\beta_X, \qquad \tilde\beta_Y = W_k^{\top}\hat\beta_Y, \qquad \tilde\Omega = W_k^{\top}\Omega W_k .$$

The **PCA-IVW estimator** is

$$\hat\theta_{\mathrm{PCA}} = \big(\tilde\beta_X^{\top}\tilde\Omega^{-1}\tilde\beta_X\big)^{-1}\tilde\beta_X^{\top}\tilde\Omega^{-1}\tilde\beta_Y .$$

It uses information from every variant, while $\tilde\Omega$ is a $k\times k$ matrix whose conditioning is controlled by discarding the directions of smallest weighted variance.

## Remarks

*2SLS equality.* The marginal slopes are $\hat\beta_Y = D^{-1}Z^{\top}Y$ and $\hat\beta_X = D^{-1}Z^{\top}X$, not the joint coefficients $H^{-1}Z^{\top}Y$ (if $Y$ is the first instrument, the joint coefficient of the second is zero while its marginal coefficient need not be). With homoscedastic outcome errors of variance $\sigma^2$, $\operatorname{Cov}(\hat\beta_Y) = \sigma^2 D^{-1}HD^{-1} = \Omega$, so $\Omega^{-1} = \sigma^{-2}DH^{-1}D$. Substituting, $\hat\beta_X^{\top}\Omega^{-1}\hat\beta_X = \sigma^{-2}X^{\top}ZH^{-1}Z^{\top}X$ and $\hat\beta_X^{\top}\Omega^{-1}\hat\beta_Y = \sigma^{-2}X^{\top}ZH^{-1}Z^{\top}Y$, because the factors $D^{-1}D$ cancel; the ratio is $\hat\theta_{\mathrm{2SLS}}$. For uncorrelated variants $H$ is diagonal, the univariable and multivariable coefficients coincide and the weights are diagonal, recovering the usual IVW formula; for correlated variants the weights carry the correlation matrix, which is what $\Omega^{-1}$ encodes.

*Why weight before PCA.* If variants were uncorrelated, $\Psi$ would be diagonal and the first principal component would be the single variant with the largest inverse-variance weight, i.e. (at equal sample sizes) the one explaining the most variance in the risk factor. With correlation, the leading components are the linear combinations of variants explaining the most variance in the risk factor; with a single causal variant one component carries all of it. Unweighted PCA of $\rho$ would instead favour directions of high linkage disequilibrium regardless of their relevance to the exposure.

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)

## Sources

- S. Burgess, V. Zuber, E. Valdes-Marquez, B. B. Sun and J. C. Hopewell, "Mendelian randomization with fine-mapped genetic data: Choosing from large numbers of correlated instrumental variables", *Genetic Epidemiology* 41 (2017), 714–725, Equations (1)–(3), section "Just right? Principal components analysis" and Appendix A.2 "Proof of equality of 2SLS and IVW estimates", <https://doi.org/10.1002/gepi.22077> (PMC5725678).
