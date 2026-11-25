# Sample variance of scores is a quadratic form

Let $X$ be a real $n \times p$ data matrix whose rows are observations. For every $w \in \mathbb{R}^p$, the sample variance of the [scores](scores.md) $s = X_c w$ along $w$ is the quadratic form of the [sample covariance matrix](sample-cov.md):

$$\frac{1}{n - 1} \sum_{i} s_i^2 = w^\top S w.$$
