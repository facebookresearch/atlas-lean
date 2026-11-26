# Exact covariance propagation for affine maps

Let $\Omega$ be finite with weights $p(\omega)$ summing to $1$, let $X : \Omega \to \mathbb R^n$, $A$ an $m \times n$ real matrix and $b \in \mathbb R^m$. With the weighted covariance matrix $\operatorname{Cov}(X)_{ij} = \sum_\omega p(\omega)\,(X_i - \mathbb E X_i)(X_j - \mathbb E X_j)$, where $\mathbb E Y = \sum_\omega p(\omega) Y(\omega)$,

$$\operatorname{Cov}(A X + b) = A \operatorname{Cov}(X) A^{\mathsf T}.$$

The weights need not be nonnegative.
