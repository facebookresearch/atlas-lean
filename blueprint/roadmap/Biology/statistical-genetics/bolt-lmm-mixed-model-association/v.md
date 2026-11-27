# Marginal phenotypic covariance matrix

For [variance components](model.md) $(K, \sigma_g^2, \sigma_e^2)$ on $n$ individuals, the marginal phenotypic covariance is the $n \times n$ matrix

$$V = \sigma_g^2 K + \sigma_e^2 \mathrm{I}.$$

It is the covariance of $y = X\beta + g + e$ when $g \sim N(0, \sigma_g^2 K)$ and $e \sim N(0, \sigma_e^2 \mathrm{I})$ are independent.
