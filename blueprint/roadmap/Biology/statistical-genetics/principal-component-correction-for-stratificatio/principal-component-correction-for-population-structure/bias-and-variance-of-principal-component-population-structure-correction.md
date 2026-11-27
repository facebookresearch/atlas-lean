# Bias and variance of principal-component population structure correction in GWAS

**Model.** Phenotypes $Y \in \mathbb{R}^n$ follow the joint linear model $Y = X\beta + \varepsilon$, $\varepsilon \sim N(0, \sigma^2 I_n)$, with a deterministic, centred and normalised genotype matrix $X \in \mathbb{R}^{n \times p}$, typically $n \ll p$. The target is the effect $\beta_1$ of one variant $X_{\cdot 1}$.

- **Population structure correction (PSC).** Take the singular value decomposition $X = \bar U\bar\Sigma\bar V^{\top}$ of the full genotype matrix (rank $\bar r$; $X^{\top}X$ is the kinship matrix) and fit $Y = X_{\cdot 1}\bar\alpha + \bar U_{1:k}\bar\gamma + \bar e$ by least squares with the top $k$ principal components.
- **Corrected population correction (CPC).** Take the SVD $X_{(-1)} = U\Sigma V^{\top}$ of the genotype matrix *without* the tested variant (rank $r$) and fit $Y = X_{\cdot 1}\alpha + U_{1:k}\gamma + e$; this is the simplest form of leave-one-chromosome-out.

Write the background signal as $X_{(-1)}\beta_{(-1)} = U\gamma$, i.e. $\gamma = \Sigma V^{\top}\beta_{(-1)}$, and the full mean as $X\beta = \bar U\bar\gamma$, i.e. $\bar\gamma = \bar\Sigma\bar V^{\top}\beta$ (all of $\beta$, including $\beta_1$). Let $P = U_{1:k}U_{1:k}^{\top}$ and $\bar P = \bar U_{1:k}\bar U_{1:k}^{\top}$, and assume the non-collinearity conditions $D = X_{\cdot 1}^{\top}(I-P)X_{\cdot 1} > 0$ and $\bar D = X_{\cdot 1}^{\top}(I-\bar P)X_{\cdot 1} > 0$, that is, the tested variant is not in the span of the chosen components, so each least-squares fit has a unique solution.

**Theorem (CPC).** The CPC estimator satisfies

$$\mathrm{bias}(\hat\alpha) = \frac{X_{\cdot 1}^{\top}U_{(k+1):r}\,\gamma_{(k+1):r}}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}U_{1:k}\|^2}, \qquad \mathrm{Var}(\hat\alpha) = \frac{\sigma^2}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}U_{1:k}\|^2} .$$

**Theorem (PSC).** The PSC estimator satisfies

$$\mathrm{bias}(\hat{\bar\alpha}) = \frac{X_{\cdot 1}^{\top}\big(\bar U_{(k+1):\bar r}\,\bar\gamma_{(k+1):\bar r} - X_{\cdot 1}\beta_1\big) + \beta_1\|X_{\cdot 1}^{\top}\bar U_{1:k}\|^2}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}\bar U_{1:k}\|^2} = \frac{X_{\cdot 1}^{\top}(I - \bar P)X_{(-1)}\beta_{(-1)}}{\bar D}, \qquad \mathrm{Var}(\hat{\bar\alpha}) = \frac{\sigma^2}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}\bar U_{1:k}\|^2}.$$

**Theorem (variance comparison).** $\mathrm{Var}(\hat\alpha) \le \mathrm{Var}(\hat{\bar\alpha})$: removing the tested variant before computing principal components never increases the variance.

The sign in the PSC numerator matters: expanding $-\beta_1\bar D$ gives $+\beta_1\|X_{\cdot 1}^{\top}\bar U_{1:k}\|^2$, and the $\beta_1$ terms cancel against $X_{\cdot 1}^{\top}(I-\bar P)X_{\cdot 1}\beta_1$, leaving the background form on the right. In particular, both estimators are unbiased when only the tested variant contributes to the mean ($\beta_{(-1)} = 0$), and both biases come only from the part of the background signal outside the chosen components. The estimators differ through the components used: those of the full $X$ partly contain the tested variant, which changes the projection $\bar P$ in the bias and lowers the residual norm $\bar D$ that sets the variance. CPC's bias vanishes when $k = r$ or the tested variant is orthogonal to the omitted components.

## Expansion

Both estimators are coefficients in an ordinary least-squares fit with orthonormal nuisance regressors, so by the Frisch–Waugh–Lovell theorem $\hat\alpha = \frac{X_{\cdot 1}^{\top}(I - P_k)Y}{X_{\cdot 1}^{\top}(I - P_k)X_{\cdot 1}}$ with $P_k$ the projection onto the chosen components, which gives the variance $\sigma^2/(\|X_{\cdot 1}\|^2 - \|X_{\cdot 1}^{\top}U_{1:k}\|^2)$ and the bias by substituting $\mathbb{E}Y = X_{\cdot 1}\beta_1 + U\gamma$ (for CPC) or $\mathbb E Y = \bar U\bar\gamma$ (for PSC), so that the bias is $[X_{\cdot 1}^{\top}(I-P_k)\mathbb E Y - \beta_1 X_{\cdot 1}^{\top}(I-P_k)X_{\cdot 1}]/X_{\cdot 1}^{\top}(I-P_k)X_{\cdot 1}$. For the variance comparison, the components of $X_{(-1)}$ explain less of $X_{\cdot 1}$ than those of $X$, which contain $X_{\cdot 1}$, so the residual norm in the denominator is larger.

## Sources

- The Tien Mai and Pierre Alquier, "Understanding the Population Structure Correction Regression", in *Proceedings of the 4th International Conference on Statistics: Theory and Applications (ICSTA 2022)*, Avestia Publishing (2022), paper 114, <https://doi.org/10.11159/icsta22.114>. Numbering as in the preprint arXiv:2108.05655v1, <https://arxiv.org/abs/2108.05655v1>: Section 2 (model, PSC and CPC), Theorems 1–3 and Appendix A.2 (proof of Theorem 2).
