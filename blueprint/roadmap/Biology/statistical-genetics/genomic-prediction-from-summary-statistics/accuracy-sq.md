# Squared accuracy of a polygenic score

In an [effect-estimate model](prsmodel.md) on a measure $\mu$ with effects $\beta_k$ and [estimated effects](beta-hat.md) $\hat\beta_k$, the squared accuracy is

$$r_g^2 = \frac{\bigl(\int \sum_k \beta_k \hat\beta_k \, d\mu\bigr)^2}{\int \sum_k \beta_k^2 \, d\mu \cdot \int \sum_k \hat\beta_k^2 \, d\mu},$$

with the convention $x/0 = 0$. By the [cross-moment identity](integral-score-mul-score.md), $\beta^\top\hat\beta$, $\beta^\top\beta$ and $\hat\beta^\top\hat\beta$ are the covariance and variances of the genetic value and the polygenic score over a target population of standardized uncorrelated markers; $r_g^2$ is a ratio of integrals, not the integral of a squared correlation.
