# Covariance linear map

Covariance of a deterministic linear map, entrywise:
`Cov(JX) i j = ∑ a, ∑ b, J i a * J j b * Cov(X) a b`.
The right side is the `(i, j)` entry of `J * Cov(X) * Jᵀ`;
covariance carries squared units and cross-covariances are retained.
