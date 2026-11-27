# Weak-instrument bias of the two-stage least-squares estimator toward the confounded association

**Model.** Let $Z \in \mathbb{R}^{n \times L}$ be a fixed matrix of $L$ genetic instruments with full column rank and projection $P_Z = Z(Z^{\top}Z)^{-1}Z^{\top}$. The exposure and outcome satisfy

$$x = Z\gamma + v, \qquad y = \beta x + u,$$

where the pairs $(u_i, v_i)$ are independent across individuals with mean zero, $\operatorname{Var}(v_i) = \sigma_v^2$ and $\operatorname{Cov}(u_i, v_i) = \sigma_{uv}$; a nonzero $\sigma_{uv}$ represents confounding of the exposure–outcome association, and instrument validity is the assumption that $Z$ is independent of $(u, v)$. The two-stage least-squares (2SLS) estimator and the concentration parameter are

$$\hat\beta_{\mathrm{2SLS}} = \frac{x^{\top}P_Z\, y}{x^{\top}P_Z\, x}, \qquad \mu^2 = \frac{\gamma^{\top}Z^{\top}Z\gamma}{\sigma_v^2}.$$

The first-stage $F$-statistic for $H_0 : \gamma = 0$ has expectation approximately $1 + \mu^2/L$.

**Proposition (first-order weak-instrument bias, as used by Burgess and Thompson 2011).** Exactly,

$$\hat\beta_{\mathrm{2SLS}} - \beta = \frac{x^{\top}P_Z u}{x^{\top}P_Z x}, \qquad \mathbb{E}[x^{\top}P_Z u] = L\,\sigma_{uv}, \qquad \mathbb{E}[x^{\top}P_Z x] = \gamma^{\top}Z^{\top}Z\gamma + L\,\sigma_v^2 .$$

Approximating the mean of the ratio by the ratio of means,

$$\mathbb{E}\big[\hat\beta_{\mathrm{2SLS}}\big] - \beta \approx \frac{\sigma_{uv}}{\sigma_v^2} \cdot \frac{L}{\mu^2 + L} \approx \frac{\sigma_{uv}}{\sigma_v^2} \cdot \frac{1}{\mathbb{E}[F]}.$$

Since the ordinary least-squares estimator of $\beta$ has asymptotic bias $\sigma_{uv}/\operatorname{Var}(x_i)$, which is close to $\sigma_{uv}/\sigma_v^2$ when the instruments explain a small share of exposure variance (the usual Mendelian randomization setting), the 2SLS bias has the same sign as the confounded observational bias and the **relative bias** is approximately $1/\mathbb{E}[F]$. Consequences: bias vanishes as $\mu^2 \to \infty$; for a fixed total instrument strength $\mu^2$, adding weak instruments (increasing $L$) increases the bias even though it lowers the variance; and $\mathbb{E}[F] \ge 10$ corresponds to relative bias of roughly $10\%$ or less.

## Depends on

- [Linear moment model for instrumental variables](linear-moment-model.md)
- [Bias of the ordinary least-squares coefficient under confounding](covariance-div-variance.md)

## Proof depends on

- [Ratio of independent normal variables is not integrable](not-integrable-div-gaussian.md)

## Expansion

Substituting $y = \beta x + u$ into $\hat\beta_{\mathrm{2SLS}}$ gives the error ratio. Because $Z$ is fixed and independent of the errors, $\mathbb{E}[x^{\top}P_Z u] = \mathbb{E}[v^{\top}P_Z u] = \sigma_{uv}\operatorname{tr}(P_Z) = L\sigma_{uv}$ and $\mathbb{E}[v^{\top}P_Z v] = L\sigma_v^2$. The fitted exposure $P_Z x$ contains the projected error $P_Z v$, which is correlated with $u$; when $\mu^2$ is small this noise is a large part of $P_Z x$, so 2SLS behaves like OLS. The ratio-of-means step is a first-order approximation, not an identity: with a single instrument ($L = 1$) the 2SLS (Wald ratio) estimator has no finite mean, and with $L \ge 2$ normal errors give finite moments only up to order $L - 1$; the approximation describes the median or trimmed-mean behaviour seen in simulation.

## Sources

- S. Burgess and S. G. Thompson, "Avoiding bias from weak instruments in Mendelian randomization studies", International Journal of Epidemiology 40 (2011), 755–764, <https://doi.org/10.1093/ije/dyr036>.
- S. Burgess and S. G. Thompson, "Bias in causal estimates from Mendelian randomization studies with weak instruments", Statistics in Medicine 30 (2011), 1312–1323, <https://doi.org/10.1002/sim.4197>.
