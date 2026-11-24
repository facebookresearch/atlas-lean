# Entries of the sample covariance matrix

Let $X$ be a real $n \times p$ data matrix whose rows are observations. The entries of the [sample covariance matrix](sample-cov.md) are

$$S_{jk} = \frac{1}{n - 1} \sum_{i=1}^n (X_{ij} - \bar x_j)(X_{ik} - \bar x_k),$$

with $(n-1)^{-1} = 0$ for $n = 1$.
