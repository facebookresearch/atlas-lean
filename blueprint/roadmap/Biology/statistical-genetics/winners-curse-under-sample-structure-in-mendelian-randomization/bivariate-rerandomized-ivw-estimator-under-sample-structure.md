# Bivariate rerandomized IVW estimator under sample structure

**Model.** Let $G_1,\dots,G_p$ be independent SNPs, $X = \sum_j \gamma_j G_j + \eta_X U + E_X$ and $Y = \beta X + \sum_j \alpha_j G_j + \eta_Y U + E_Y$, so the SNP–outcome effect is $\Gamma_j = \beta\gamma_j + \alpha_j$. Two-sample summary statistics satisfy, independently across SNPs,

$$\begin{pmatrix}\hat\gamma_j\\ \hat\Gamma_j\end{pmatrix} \sim N\!\left(\begin{pmatrix}\gamma_j\\ \Gamma_j\end{pmatrix}, \begin{pmatrix}\sigma_{\hat\gamma_j}^2 & \rho\,\sigma_{\hat\gamma_j}\sigma_{\hat\Gamma_j}\\ \rho\,\sigma_{\hat\gamma_j}\sigma_{\hat\Gamma_j} & \sigma_{\hat\Gamma_j}^2\end{pmatrix}\right),$$

where the correlation $\rho$ is induced by sample structure (residual stratification, sample overlap) and the working standard errors are calibrated by LD score regression intercepts ($\rho = c_{12}/\sqrt{c_1c_2}$). Pleiotropy is balanced and InSIDE: the $\alpha_j$ are independent, mean zero, with variance $\tau_\alpha^2$, independent of the $\gamma_j$.

**Randomized selection.** With pseudo-associations $Z_j \sim N(0,\eta^2)$, select $\mathcal{S}_\lambda = \{j : |\hat\gamma_j/\sigma_{\hat\gamma_j} + Z_j| > \lambda\}$ and write $A_{j,\pm} = -\hat\gamma_j/(\sigma_{\hat\gamma_j}\eta) \pm \lambda/\eta$ and $M_j = \dfrac{\phi(A_{j,+}) - \phi(A_{j,-})}{1 - \Phi(A_{j,+}) + \Phi(A_{j,-})}$.

**Outcome-side winner's curse.** If $\rho \ne 0$, exposure-based selection shifts the outcome estimate:

$$\mathbb{E}[\hat\Gamma_j \mid j \in \mathcal{S}_\lambda] = \Gamma_j + \frac{\rho\,\sigma_{\hat\Gamma_j}}{\Pr(j\in\mathcal{S}_\lambda)\sqrt{1+\eta^2}}\left[\phi\!\Big(\tfrac{\lambda - \gamma_j/\sigma_{\hat\gamma_j}}{\sqrt{1+\eta^2}}\Big) - \phi\!\Big(\tfrac{-\lambda - \gamma_j/\sigma_{\hat\gamma_j}}{\sqrt{1+\eta^2}}\Big)\right],$$

a bias linear in $|\rho|$ that vanishes when $\rho = 0$.

**Rao–Blackwellized estimates.** The estimates

$$\hat\gamma_{j,\mathrm{RB}} = \hat\gamma_j - \frac{\sigma_{\hat\gamma_j}}{\eta}M_j, \qquad \hat\Gamma_{j,\mathrm{RB}} = \hat\Gamma_j - \frac{\rho\,\sigma_{\hat\Gamma_j}}{\eta}M_j$$

are conditionally unbiased for $\gamma_j$ and $\Gamma_j$ given selection, and their post-selection covariance is estimated unbiasedly by

$$\hat\sigma_{j,\mathrm{RB}} = \rho\,\sigma_{\hat\gamma_j}\sigma_{\hat\Gamma_j}\left[1 - \frac{1}{\eta^2}\frac{A_{j,+}\phi(A_{j,+}) - A_{j,-}\phi(A_{j,-})}{1 - \Phi(A_{j,+}) + \Phi(A_{j,-})} + \frac{M_j^2}{\eta^2}\right].$$

**Estimator and theorem.** The bivariate RIVW estimator is

$$\hat\beta_{\mathrm{BRIVW}} = \frac{\sum_{j\in\mathcal{S}_\lambda}\sigma_{\hat\Gamma_j}^{-2}\big(\hat\Gamma_{j,\mathrm{RB}}\hat\gamma_{j,\mathrm{RB}} - \hat\sigma_{j,\mathrm{RB}}\big)}{\sum_{j\in\mathcal{S}_\lambda}\sigma_{\hat\Gamma_j}^{-2}\big(\hat\gamma_{j,\mathrm{RB}}^2 - \hat\sigma^2_{\hat\gamma_{j,\mathrm{RB}}}\big)}.$$

Let $p_\lambda = |\mathcal{S}_\lambda|$ and $\kappa_\lambda = p_\lambda^{-1}\sum_{j\in\mathcal{S}_\lambda}(\gamma_j/\sigma_{\hat\gamma_j})^2$. If $p_\lambda \to \infty$ and $\kappa_\lambda\sqrt{p_\lambda} \to \infty$ in probability, then conditional on $\mathcal{S}_\lambda$, $\hat\beta_{\mathrm{BRIVW}} \to \beta$ in probability, and under a further Lindeberg-type condition $\hat V_{\mathrm{BRIVW}}^{-1/2}(\hat\beta_{\mathrm{BRIVW}} - \beta) \to N(0,1)$. With $\rho = 0$ and unit LDSC intercepts it reduces to the RIVW estimator.

## Expansion

Adding independent noise $Z_j$ before thresholding makes $\hat\gamma_j - (\sigma_{\hat\gamma_j}/\eta^2)Z_j$ independent of the selection event; when $\rho \ne 0$ the outcome estimate is correlated with the selection statistic with covariance $\rho\sigma_{\hat\Gamma_j}$, so the analogous correction $\hat\Gamma_j - (\rho\sigma_{\hat\Gamma_j}/\eta^2)Z_j$ is needed. Conditioning these initial estimators on the observed statistics and on selection (Rao–Blackwellization) gives the closed forms, which involve truncated-normal moments. Subtracting the estimated post-selection covariance removes the bias of $\hat\gamma_{j,\mathrm{RB}}\hat\Gamma_{j,\mathrm{RB}}$, and subtracting $\hat\sigma^2_{\hat\gamma_{j,\mathrm{RB}}}$ in the denominator removes weak-instrument bias. The denominator is equivalent to $\sum \sigma_{\hat\Gamma_j}^{-2}\gamma_j^2 = \Theta_p(\kappa_\lambda p_\lambda)$, while the numerator fluctuation has variance $\Theta_p\{p_\lambda v^4(\kappa_\lambda + 1)\}$, giving consistency when $\kappa_\lambda\sqrt{p_\lambda} \to \infty$.

## Sources

- Xin Liu, Youpeng Su, Chuchu Zeng, Yilei Ma, Siqi Xu, Ping Yin and Peng Wang, "Simultaneously accounting for the winner's curse and sample structure in Mendelian randomization: bivariate rerandomized inverse variance weighted estimator", arXiv:2603.06078 (2026), Section 2 (Assumptions 1–3), Section 3 (RIVW), Section 4 (Lemma 1, the BRIVW construction, Theorem 1) and Appendices A–C (Lemmas 2–11), <https://doi.org/10.48550/arXiv.2603.06078>.
