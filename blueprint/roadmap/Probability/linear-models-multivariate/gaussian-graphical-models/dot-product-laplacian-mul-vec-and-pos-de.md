# Weighted graph Laplacians and the Leroux precision matrix

Let $W$ be a symmetric real matrix of weights on a finite index set and $L = \operatorname{diag}(W\mathbf{1}) - W$, where $(W\mathbf{1})_i = \sum_j w_{ij}$. Then:

- $z^\top L z = \frac12 \sum_i \sum_j w_{ij}(z_i - z_j)^2$ for every $z$ (symmetry suffices; the diagonal of $W$ may be nonzero, since it cancels);
- if moreover $w_{ij} \ge 0$ for all $i, j$ and $0 \le \rho < 1$, then $Q = \rho L + (1 - \rho) I$ satisfies $(1 - \rho) \sum_i z_i^2 \le z^\top Q z$ for every $z$, and $Q$ is positive definite;
- $Q \mathbf{1} = (1 - \rho)\mathbf{1}$ for every real $\rho$, since the rows of $L$ sum to zero.

$Q/v$ is the precision matrix of the Leroux conditional autoregressive model.
