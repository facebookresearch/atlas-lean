# Dudbridge's variance explained by a cross-trait polygenic score

Let $G = (G_1, \dots, G_m)$ be independent standardized markers ($\mathbb{E}G_i = 0$, $\operatorname{Var}G_i = 1$) and let two traits be

$$Y_1 = \sum_{i=1}^{m}\beta_{i1}G_i + E_1, \qquad Y_2 = \sum_{i=1}^{m}\beta_{i2}G_i + E_2,$$

with errors independent of $G$. Over markers, the effects are random with $\mathbb{E}\beta_{ij} = 0$, $\operatorname{Var}\beta_{i1} = \sigma_1^2$, $\operatorname{Var}\beta_{i2} = \sigma_2^2$, $\operatorname{cov}(\beta_{i1}, \beta_{i2}) = \sigma_{12}$. Effects on $Y_1$ are estimated in a training sample of size $n_1$ as $\hat\beta_{i1} = \beta_{i1} + \epsilon_{i1}$, with $\epsilon_{i1}$ of variance $n_1^{-1}$, independent of the effects and of the target sample. In an independent target sample, form the polygenic score $\hat S = \sum_{i=1}^{m}\hat\beta_{i1}G_i$ using all markers.

**Statement.**

$$\operatorname{Var}(\hat S) = m\,(\sigma_1^2 + n_1^{-1}), \qquad \operatorname{cov}(\hat S, Y_2) = m\,\sigma_{12},$$

so the proportion of variance of $Y_2$ explained by the score is

$$R^2_{\hat S, Y_2} = \frac{\operatorname{cov}(\hat S, Y_2)^2}{\operatorname{Var}(\hat S)\operatorname{Var}(Y_2)} = \frac{m\,\sigma_{12}^2}{(\sigma_1^2 + n_1^{-1})\operatorname{Var}(Y_2)}.$$

For the same standardized trait in both samples ($\sigma_{12} = \sigma_1^2 = \sigma_g^2/m$, $\operatorname{Var}(Y_2) = 1$) this becomes

$$R^2 = \frac{\sigma_g^4}{\sigma_g^2 + m/n_1} = \sigma_g^2\cdot\frac{n_1\sigma_g^2}{n_1\sigma_g^2 + m},$$

the [Daetwyler–Dudbridge accuracy](accuracy-sq-eq-of-s2.md) multiplied by $\sigma_g^2$, since the score predicts the phenotype rather than the genetic value. Shrinking all estimates by a common factor $A > 0$, as in the normal-prior posterior mean $A\hat\beta_{i1}$ with $A = \sigma_1^2/(\sigma_1^2 + n_1^{-1})$, leaves $R^2$ (and the power of the association test of the score) unchanged while reducing mean squared error.

## Depends on

- [Effect-estimate model for polygenic score accuracy](prsmodel.md)
- [Daetwyler–Dudbridge formula](accuracy-sq-eq-of-s2.md)

## Expansion

Since the $G_i$ are independent with unit variance and independent of the estimates, $\mathbb{E}[\hat S^2] = \sum_i\mathbb{E}[\hat\beta_{i1}^2] = m(\sigma_1^2 + n_1^{-1})$ and $\mathbb{E}[\hat S\,Y_2] = \sum_i\mathbb{E}[\hat\beta_{i1}\beta_{i2}] = m\sigma_{12}$, the estimation error being independent of $\beta_{i2}$. A correlation is invariant under positive rescaling of either variable, which gives the shrinkage remark. The paper extends these moments to scores restricted to markers with $P$-values in a window, using truncated-normal moments of $\hat\beta_{i1}$, and to binary traits through the liability-threshold model.

## Sources

- F. Dudbridge, "Power and predictive accuracy of polygenic risk scores", PLoS Genetics 9 (2013), e1003348, Methods, "Quantitative model" and "Shrinkage estimation", <https://doi.org/10.1371/journal.pgen.1003348> (PMC3605113).
