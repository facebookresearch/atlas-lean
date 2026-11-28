# Average log-likelihood of a finite-rank model

Let the log-likelihood have finite rank: $\ell_\theta(x) = \sum_{j<m}a_j(\theta)g_j(x)$. Then $\frac1n\sum_{i<n}\ell_\theta(X_i) = \sum_j a_j(\theta)\cdot\frac1n\sum_{i<n}g_j(X_i)$ for every sample, $n$ and $\theta$.
