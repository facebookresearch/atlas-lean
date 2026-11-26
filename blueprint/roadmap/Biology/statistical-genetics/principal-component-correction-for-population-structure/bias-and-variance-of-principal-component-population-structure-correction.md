# Bias and variance of principal-component population structure correction in GWAS

**Model.** Phenotypes $Y \in \mathbb{R}^n$ follow the joint linear model $Y = X\beta + \varepsilon$, $\varepsilon \sim N(0, \sigma^2 I_n)$, with a deterministic, centred and normalised genotype matrix $X \in \mathbb{R}^{n \times p}$, typically $n \ll p$. The target is the effect $\beta_1$ of one variant $X_{\cdot 1}$.

- **Population structure correction (PSC).** Take the singular value decomposition $X = \bar U\bar\Sigma\bar V^{\top}$ of the full genotype matrix (rank $\bar r$; $X^{\top}X$ is the kinship matrix) and fit $Y = X_{\cdot 1}\bar\alpha + \bar U_{1:k}\bar\gamma + \bar e$ by least squares with the top $k$ principal components.
- **Corrected population correction (CPC).** Take the SVD $X_{(-1)} = U\Sigma V^{\top}$ of the genotype matrix *without* the tested variant (rank $r$) and fit $Y = X_{\cdot 1}\alpha + U_{1:k}\gamma + e$; this is the simplest form of leave-one-chromosome-out.

Write the background signal as $X_{(-1)}\beta_{(-1)} = U\gamma$, i.e. $\gamma = \Sigma V^{\top}\beta_{(-1)}$, and similarly $\bar\gamma$ for the full decomposition.

**Theorem (CPC).** The CPC estimator satisfies
$$\mathrm{bias}(\hat\alpha) = \frac{X_{\cdot 1}^{\top}U_{(k+1):r}\,\gamma_{(k+1):r}}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}U_{1:k}\|^2}, \qquad \mathrm{Var}(\hat\alpha) = \frac{\sigma^2}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}U_{1:k}\|^2} .$$

**Theorem (PSC).** The PSC estimator satisfies
$$\mathrm{bias}(\hat{\bar\alpha}) = \frac{X_{\cdot 1}^{\top}\big(\bar U_{(k+1):\bar r}\,\bar\gamma_{(k+1):\bar r} - X_{\cdot 1}\beta_1\big) - \beta_1\|X_{\cdot 1}^{\top}\bar U_{1:k}\|^2}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}\bar U_{1:k}\|^2}, \qquad \mathrm{Var}(\hat{\bar\alpha}) = \frac{\sigma^2}{X_{\cdot 1}^{\top}X_{\cdot 1} - \|X_{\cdot 1}^{\top}\bar U_{1:k}\|^2}.$$

**Theorem (variance comparison).** $\mathrm{Var}(\hat\alpha) \le \mathrm{Var}(\hat{\bar\alpha})$: removing the tested variant before computing principal components never increases the variance.

So PSC is biased even when the leading components capture all the structure, because the components computed from the full $X$ partly contain the tested variant itself and absorb part of its effect (the $\beta_1$ terms), while CPC's bias comes only from background signal outside the top $k$ components and vanishes when $k = r$ or the tested variant is orthogonal to the omitted components.

## Expansion

Both estimators are coefficients in an ordinary least-squares fit with orthonormal nuisance regressors, so by the Frisch–Waugh–Lovell theorem $\hat\alpha = \frac{X_{\cdot 1}^{\top}(I - P_k)Y}{X_{\cdot 1}^{\top}(I - P_k)X_{\cdot 1}}$ with $P_k$ the projection onto the chosen components, which gives the variance $\sigma^2/(\|X_{\cdot 1}\|^2 - \|X_{\cdot 1}^{\top}U_{1:k}\|^2)$ and the bias by substituting $\mathbb{E}Y = X_{\cdot 1}\beta_1 + U\gamma$. For the variance comparison, the components of $X_{(-1)}$ explain less of $X_{\cdot 1}$ than those of $X$, which contain $X_{\cdot 1}$, so the residual norm in the denominator is larger.

## Sources

- The Tien Mai and Pierre Alquier, "Understanding the population structure correction regression", arXiv:2108.05655 (2021), Section 2 (model, PSC and CPC) and Theorems 1–3, <https://doi.org/10.48550/arXiv.2108.05655>.
