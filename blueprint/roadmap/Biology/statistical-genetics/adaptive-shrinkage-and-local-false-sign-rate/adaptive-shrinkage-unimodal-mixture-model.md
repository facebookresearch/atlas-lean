# Adaptive shrinkage model with a unimodal mixture prior

Let $\hat\beta_1, \dots, \hat\beta_J$ be estimates of effects $\beta_1, \dots, \beta_J$ with standard errors $\hat s_1, \dots, \hat s_J > 0$. The adaptive shrinkage (ash) model assumes:

1. **Unimodal prior.** The $\beta_j$ are independent draws from

$$g(\cdot\,; \pi) = \pi_0\,\delta_0 + \sum_{k=1}^K \pi_k\,\mathcal N(0, \sigma_k^2),$$

where $\sigma_1 < \dots < \sigma_K$ is a fixed, large and dense grid of positive numbers and $\pi = (\pi_0, \dots, \pi_K)$ are nonnegative mixture proportions summing to $1$.
2. **Normal likelihood.** $\hat\beta_j \mid \beta_j \sim \mathcal N(\beta_j, \hat s_j^2)$ independently.

Then, with $\sigma_0 := 0$, the $\hat\beta_j$ are independent with marginal likelihood

$$L(\pi) = \prod_{j=1}^J \sum_{k=0}^K \pi_k\,\mathcal N\big(\hat\beta_j; 0, \sigma_k^2 + \hat s_j^2\big),$$

which is log-concave on the simplex (its logarithm $\log L(\pi) = \sum_j \log \sum_k \pi_k \mathcal{N}(\hat{\beta}_j; 0, \sigma_k^2 + \hat{s}_j^2)$ is concave in $\pi$ on the simplex), so $\hat\pi$ solves a convex optimization problem. Given $\hat\pi$, each posterior $p(\beta_j \mid \hat\beta_j, \hat s_j, \hat\pi)$ is a mixture of a point mass at $0$ and $K$ normal distributions. In practice $\hat\pi$ maximizes a penalized likelihood that keeps $\hat\pi_0$ as large as the data allow, to avoid underestimating the null proportion.

## Expansion

Integrating $\beta_j \sim \mathcal N(0, \sigma_k^2)$ against the normal likelihood gives $\mathcal N(0, \sigma_k^2 + \hat s_j^2)$ for each component. Because the grid is fixed, $\log L(\pi) = \sum_j \log(\sum_k \pi_k c_{jk})$ with fixed $c_{jk} > 0$ is a sum of logarithms of linear functions of $\pi$, hence concave; interior-point methods or EM solve it. Within component $k \ge 1$, the posterior of $\beta_j$ is $\mathcal N\big(\frac{\sigma_k^2}{\sigma_k^2+\hat s_j^2}\hat\beta_j, \frac{\sigma_k^2\hat s_j^2}{\sigma_k^2+\hat s_j^2}\big)$, so shrinkage adapts both to the estimated signal distribution and to each measurement's precision. Replacing normals by uniforms allows asymmetric unimodal $g$.

## Sources

- M. Stephens, "False discovery rates: a new deal", Biostatistics 18 (2017), 275–294, <https://doi.org/10.1093/biostatistics/kxw041> (PMC5379932). Section 2, Equations (2.1)–(2.8).
