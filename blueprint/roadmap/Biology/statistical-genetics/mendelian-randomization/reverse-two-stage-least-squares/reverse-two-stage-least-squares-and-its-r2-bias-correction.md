# Reverse two-stage least squares and its $R^2$ bias correction

**Model.** Let $X \in \mathbb{R}$ be an exposure (e.g. gene expression), $Y \in \mathbb{R}$ an outcome and $Z \in \mathbb{R}^p$ genetic instruments (SNPs). Two independent samples are observed: $\mathbb{D}_1 = (x_1, Z_1)$ of size $n_1$ and $\mathbb{D}_2 = (y_2, Z_2)$ of size $n_2$, with $p$ fixed and typically $n_2 \gg n_1$, all variables standardised. The structural model is

$$x = Z\beta + \varepsilon, \qquad y = x\,\theta + \xi,$$

with mean-zero normal errors $\varepsilon, \xi$ independent of $Z$ (but possibly correlated with each other through confounding), the same model holding in both samples. The causal effect is $\theta$.

**Reverse 2SLS (r2SLS).** Since $y_2 = Z_2\beta\theta + \varepsilon\theta + \xi$, regress $y_2$ on $Z_2$ by OLS to get $\widetilde{\beta\theta}$, predict the outcome in sample 1 as $\hat y_1 = Z_1\widetilde{\beta\theta}$, and regress the observed exposure-sample data on it through the working model $\hat y_1 = x_1\theta + \text{error}$:

$$\hat\theta = \frac{x_1^{\top}\hat y_1}{x_1^{\top}x_1}.$$

**Decomposition (Eq. 4).** Writing $x_1 = Z_1\beta + \varepsilon$,

$$\hat\theta = \theta - \theta\,\frac{\varepsilon^{\top}\varepsilon}{x_1^{\top}x_1} - \theta\,\frac{(Z_1\beta)^{\top}\varepsilon}{x_1^{\top}x_1} + \frac{x_1^{\top}Z_1(\widetilde{\beta\theta} - \beta\theta)}{x_1^{\top}x_1}.$$

Hence $\hat\theta$ is unbiased under $H_0 : \theta = 0$, and for $\theta \ne 0$ its bias comes from the factor $\kappa = \varepsilon^{\top}\varepsilon / x_1^{\top}x_1$, the unexplained fraction of stage-1 variance, which is approximately $1 - R^2$ with $R^2$ the population stage-1 coefficient of determination of $x$ on $Z$.

**Corrected estimator.** $\tilde\theta = \hat\theta/(1 - \kappa)$, with $1 - \kappa$ estimated by the Olkin–Pratt or adjusted $R^2$ of the stage-1 regression; as $n_1 \to \infty$, $1 - \kappa$ converges to the population $R^2$, and Theorem 1 gives the asymptotic normal distribution of $\tilde\theta$ including the extra variance term $(Z_1\beta)^{\top}\varepsilon\,\theta/x_1^{\top}x_1$.

## Depends on

- [Linear moment model for instrumental variables](../linear-moment-model.md)

## Expansion

Substituting $\hat y_1 = Z_1\beta\theta + Z_1(\widetilde{\beta\theta} - \beta\theta)$ and $Z_1\beta = x_1 - \varepsilon$ gives $x_1^{\top}Z_1\beta = x_1^{\top}x_1 - \varepsilon^{\top}\varepsilon - (Z_1\beta)^{\top}\varepsilon$, which yields the decomposition. The term $(Z_1\beta)^{\top}\varepsilon$ has mean zero because $\varepsilon$ is independent of $Z_1$, while $\varepsilon^{\top}\varepsilon/x_1^{\top}x_1$ estimates the unexplained stage-1 variance fraction: the genetically predicted outcome only carries the heritable part of the exposure, so regressing the full exposure on it attenuates the slope by $R^2$. Unlike two-stage least squares, which uses the predicted exposure as a regressor and so suffers from weak-instrument bias toward the confounded estimate, the predicted quantity here is the response, so the stage-1 sample appears only through $x_1$, and type I error under $\theta = 0$ is controlled without bias correction. Uncorrected sample $R^2$ overstates $1 - \kappa$, which is why an unbiased $R^2$ estimator is used when instruments are weak.

## Sources

- L. Fang, W. Pan, "A Modification to Two-Stage Least Squares With Genetic Applications", Statistics in Medicine (2025), Section 2, Eqs. (1)–(4) and Theorem 1, <https://doi.org/10.1002/sim.70308>, PMCID PMC12593333.
