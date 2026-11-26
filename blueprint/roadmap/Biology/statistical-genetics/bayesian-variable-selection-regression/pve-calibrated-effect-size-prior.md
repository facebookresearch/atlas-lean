# Prior on effect size calibrated by the proportion of variance explained

In the [BVSR model](bayesian-variable-selection-regression-model.md) with centered covariates, let $s_j=\frac1n\sum_{i=1}^nx_{ij}^2$ be the variance of covariate $j$. The variance of the genetic predictor relative to the residual variance and the proportion of variance explained (PVE) are

$$V(\beta,\tau)=\frac1n\sum_{i=1}^n\bigl[(X\beta)_i\bigr]^2\tau,\qquad \mathrm{PVE}(\beta,\tau)=\frac{V(\beta,\tau)}{1+V(\beta,\tau)}.$$

Under $\beta_\gamma\mid\tau,\gamma\sim N(0,(\sigma_a^2/\tau)I)$,

$$v(\gamma,\sigma_a):=E\bigl[V(\beta,\tau)\mid\gamma,\sigma_a,\tau\bigr]=\sigma_a^2\sum_{j:\gamma_j=1}s_j .$$

Set $h(\gamma,\sigma_a)=v/(1+v)$ and give $h$ a $U(0,1)$ prior independent of $\gamma$. This induces the prior on $\sigma_a$ given $\gamma$

$$\sigma_a^2(h,\gamma)=\frac{h}{1-h}\,\frac1{\sum_{j:\gamma_j=1}s_j},$$

so models with more included variants receive more shrinkage per effect, and the implied prior on the PVE is roughly flat on $(0,1)$ whatever the model size. The induced variable $Z=h/(1-h)$ has density $f(z)=(1+z)^{-2}$ on $(0,\infty)$, which is heavy-tailed.

## Depends on

- [Bayesian variable selection regression model](bayesian-variable-selection-regression-model.md)

## Expansion

$E[(X\beta)_i^2]=\sum_{j\in\gamma}x_{ij}^2\sigma_a^2/\tau$ because the included coefficients are independent with variance $\sigma_a^2/\tau$; averaging over $i$ and multiplying by $\tau$ gives $v$. Solving $h=v/(1+v)$ for $\sigma_a^2$ gives the displayed relation. If $h\sim U(0,1)$ then $\Pr(Z\le z)=\Pr(h\le z/(1+z))=z/(1+z)$, whose derivative is $(1+z)^{-2}$. The usual alternative, $\sigma_a$ independent of $\gamma$, makes the expected PVE grow with $|\gamma|$, so large models are a priori forced to explain much more variance; $h$ is a ratio of expectations, not exactly $E[\mathrm{PVE}]$. Posterior samples of $\mathrm{PVE}(\beta,\tau)$ estimate the total signal even when individual causal variants cannot be identified.

## Sources

- Y. Guan, M. Stephens, *Bayesian variable selection regression for genome-wide association studies and other large-scale problems*, The Annals of Applied Statistics 5 (2011), 1780–1815, <https://doi.org/10.1214/11-AOAS455>. Section 2.1, equations (2.9)–(2.13), and Section 3.2.
