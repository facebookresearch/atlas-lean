# Best linear unbiased predictor of genetic effects

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with [phenotypic covariance](v.md) $V$, let $X$ be a real $n \times p$ matrix and let $y \in \mathbb{R}^n$. The best linear unbiased predictor (BLUP) of the genetic effects is

$$\hat g = \sigma_g^2 K\, V^{-1} (y - X\hat\beta) \in \mathbb{R}^n,$$

where $\hat\beta$ is the [generalized least-squares estimator](gls.md). The name follows Henderson (1975); the optimality property is not part of the definition.

## Sources

- C. R. Henderson, *Best linear unbiased estimation and prediction under a selection model*, Biometrics 31 (1975), 423–447.
