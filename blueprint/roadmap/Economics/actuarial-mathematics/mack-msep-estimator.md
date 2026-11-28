# Mack's estimator of the mean squared error of prediction of the chain-ladder reserve

In the setting of the [chain-ladder forecast under Mack's assumptions](mack-chain-ladder-conditional-forecast.md), with cumulative claims $C_{i,k}$, $0 \le i, k \le n$, observed for $i + k \le n$, add Mack's variance assumption $\operatorname{Var}(C_{i,k+1} \mid C_{i,0}, \dots, C_{i,k}) = \sigma_k^2\, C_{i,k}$. Assume $n \ge 3$, that every observed $C_{i,k}$ is positive, so that every $\hat f_k$ and every forecast $\hat C_{i,k}$ below is positive and every denominator is nonzero, and that $\hat\sigma_{n-3}^2 > 0$, so that the extrapolation below is defined. Define the chain-ladder factors and variance parameters

$$\hat f_k = \frac{\sum_{j=0}^{n-k-1} C_{j,k+1}}{\sum_{j=0}^{n-k-1} C_{j,k}}, \qquad \hat\sigma_k^2 = \frac{1}{n-k-1} \sum_{j=0}^{n-k-1} C_{j,k} \Bigl(\frac{C_{j,k+1}}{C_{j,k}} - \hat f_k\Bigr)^2 \quad (k \le n-2),$$

with Mack's extrapolation $\hat\sigma_{n-1}^2 = \min\bigl(\hat\sigma_{n-2}^4 / \hat\sigma_{n-3}^2, \min(\hat\sigma_{n-3}^2, \hat\sigma_{n-2}^2)\bigr)$, and the forecasts $\hat C_{i,k} = C_{i,n-i} \prod_{j=n-i}^{k-1} \hat f_j$ for $k \ge n - i$. Mack's estimator of the conditional mean squared error of prediction of the ultimate claims of accident year $i$, combining process variance and parameter estimation error, is

$$\widehat{\mathrm{msep}}(\hat C_{i,n}) = \hat C_{i,n}^2 \sum_{k=n-i}^{n-1} \frac{\hat\sigma_k^2}{\hat f_k^2} \Bigl(\frac{1}{\hat C_{i,k}} + \frac{1}{\sum_{j=0}^{n-k-1} C_{j,k}}\Bigr),$$

and for the total reserve $\hat R = \sum_i (\hat C_{i,n} - C_{i,n-i})$ it adds the covariance terms between accident years, which come from the shared estimated factors:

$$\widehat{\mathrm{msep}}(\hat R) = \sum_{i} \widehat{\mathrm{msep}}(\hat C_{i,n}) + \sum_{i} \hat C_{i,n} \Bigl(\sum_{j > i} \hat C_{j,n}\Bigr) \sum_{k=n-i}^{n-1} \frac{2\hat\sigma_k^2 / \hat f_k^2}{\sum_{l=0}^{n-k-1} C_{l,k}}.$$

These are estimators derived under the stated assumptions with approximations for the parameter-error term; they are not exact identities.

## Depends on

- [Chain-ladder forecast under Mack's conditional-mean assumptions](mack-chain-ladder-conditional-forecast.md)

## Expansion

This page becomes ready once:

- the exact process-variance formula $\operatorname{Var}(C_{i,n} \mid \mathcal D) = C_{i,n-i} \sum_{k=n-i}^{n-1} \bigl(\prod_{j=n-i}^{k-1} f_j\bigr)\, \sigma_k^2 \bigl(\prod_{j=k+1}^{n-1} f_j^2\bigr)$ and the decomposition of the conditional mean squared error of prediction into process variance plus squared estimation error are stated as results (statement prerequisite)
- unbiasedness of $\hat f_k$ and $\hat\sigma_k^2$ given the past, and the approximation used for the parameter-error term, are stated as separate results

## Sources

- T. Mack, "Distribution-free calculation of the standard error of chain ladder reserve estimates", *ASTIN Bulletin* 23(2):213–225, 1993
