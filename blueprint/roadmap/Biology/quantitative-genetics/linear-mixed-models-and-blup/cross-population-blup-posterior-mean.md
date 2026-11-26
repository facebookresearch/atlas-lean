# Cross-population BLUP with a genetic correlation (XPA)

Let two independent samples follow $y_1 = Z_1 \omega_1 + X_1 \beta_1 + \varepsilon$ and $y_2 = Z_2 \omega_2 + X_2 \beta_2 + \xi$, with $X_1 \in \mathbb R^{n_1 \times p}$, $X_2 \in \mathbb R^{n_2 \times p}$ standardized genotype matrices on the same $p$ SNPs, $\varepsilon \sim N(0, \sigma_\varepsilon^2 I_{n_1})$ and $\xi \sim N(0, \sigma_\xi^2 I_{n_2})$ independent, and SNP effects independent across SNPs with

$$\begin{pmatrix} \beta_{1,j} \\ \beta_{2,j} \end{pmatrix} \sim N(0, \Sigma_\beta), \qquad \Sigma_\beta = \begin{pmatrix} \sigma_1^2 & \delta \\ \delta & \sigma_2^2 \end{pmatrix}, \quad \delta = \rho\, \sigma_1 \sigma_2,$$

$\Sigma_\beta$ positive definite. Order $\beta = (\beta_1^\top, \beta_2^\top)^\top$, let $X = \operatorname{diag}(X_1, X_2)$, $y - Z\omega = ((y_1 - Z_1\omega_1)^\top, (y_2 - Z_2\omega_2)^\top)^\top$, and

$$\Delta = \begin{pmatrix} \sigma_\varepsilon^2 & 0 \\ 0 & \sigma_\xi^2 \end{pmatrix} \Sigma_\beta^{-1}.$$

Then, for fixed $\omega$ and variance parameters, $\beta \mid y \sim N(\mu, \Lambda^{-1})$ with $\Lambda = \operatorname{diag}(X_1^\top X_1/\sigma_\varepsilon^2, X_2^\top X_2/\sigma_\xi^2) + \Sigma_\beta^{-1} \otimes I_p$ and

$$\mu = \bigl(X^\top X + \Delta \otimes I_p\bigr)^{-1} X^\top (y - Z\omega) = (\Delta^{-1} \otimes I_p)\, X^\top \bigl(I_{n_1 + n_2} + X (\Delta^{-1} \otimes I_p) X^\top\bigr)^{-1} (y - Z\omega).$$

The second form needs only an $(n_1 + n_2)$-dimensional solve. The target-population predictor is $X_1^{\text{new}} \mu_1$; when $\rho \ne 0$ the auxiliary sample enters $\mu_1$ through the off-diagonal block of $\Delta$.

## Expansion

With $D = \operatorname{diag}(\sigma_\varepsilon^2, \sigma_\xi^2) \otimes I_p$ one has $\Lambda = D^{-1}(X^\top X + \Delta \otimes I_p)$ and the Gaussian posterior mean $\Lambda^{-1} D^{-1} X^\top (y - Z\omega)$, giving the first form. The second is the push-through identity $(X^\top X + M)^{-1} X^\top = M^{-1} X^\top (I + X M^{-1} X^\top)^{-1}$ with $M = \Delta \otimes I_p$.

## Depends on

- [BLUP is the conditional expectation](cond-exp-mixed-model.md)

## Proof depends on

None beyond the Gaussian posterior of a linear model with a Gaussian prior and the push-through identity, as the Expansion describes.

## Sources

- M. Cai, J. Xiao, S. Zhang et al., "A unified framework for cross-population trait prediction by leveraging the genetic correlation of polygenic traits", *American Journal of Human Genetics* 108 (2021), <https://doi.org/10.1016/j.ajhg.2021.03.002> (PMC8059341). Equations 1 and 2; Appendix A, equations A2 and A3.
