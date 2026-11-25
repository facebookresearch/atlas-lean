# Trace of the sample covariance is the total sample variance

Let $X$ be a real $n \times p$ data matrix whose rows are observations. The trace of the [sample covariance matrix](sample-cov.md) is the total sample variance, the sum of the column sample variances:

$$\operatorname{tr} S = \sum_{j} \frac{1}{n - 1} \sum_{i} (X_{ij} - \bar x_j)^2.$$
