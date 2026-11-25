# Effect-estimate model for polygenic score accuracy

Let $\mu$ be a measure on a measurable space $\Omega$ and let $M$ be a natural number (the number of markers). An effect-estimate model consists of real numbers $h^2$ (the SNP heritability) and $s^2$ (the sampling variance of each estimate), and real functions $\beta_1, \dots, \beta_M$ (the effects) and $e_1, \dots, e_M$ (the estimation errors) on $\Omega$, all square integrable with respect to $\mu$, such that for all $k, l$

- $\int \beta_k \beta_l \, d\mu = h^2 / M$ if $k = l$ and $0$ otherwise;
- $\int e_k e_l \, d\mu = s^2$ if $k = l$ and $0$ otherwise;
- $\int \beta_k e_l \, d\mu = 0$.

The estimated effects are $\hat\beta_k = \beta_k + e_k$. When $\mu$ is a probability measure and the effects and errors have mean zero, these are the covariance conditions of the model of Daetwyler et al. (2008) and Dudbridge (2013).

## Sources

- H. D. Daetwyler, B. Villanueva, J. A. Woolliams, *Accuracy of predicting the genetic risk of disease using a genome-wide approach*, PLoS ONE 3 (2008), e3395.
- F. Dudbridge, *Power and predictive accuracy of polygenic risk scores*, PLoS Genet. 9 (2013), e1003348.
