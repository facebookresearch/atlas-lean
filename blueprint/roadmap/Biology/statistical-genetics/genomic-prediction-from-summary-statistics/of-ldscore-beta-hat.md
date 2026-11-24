# Estimates of the derived model are normalized scores

Let $(h^2, \beta, \varepsilon)$ be an [LD-score model](../ld-score-regression/model.md) with $N \ne 0$ individuals and $M$ markers, and let $X$ be a real $N \times M$ matrix with [orthogonal standardized columns](has-orthogonal-columns.md). Then for every marker $k$, the estimated effect $\beta_k + e_k$ of the [derived effect-estimate model](of-ldscore.md) equals the normalized score

$$\frac{1}{N} \sum_{i=1}^{N} X_{ik}\, y_i, \qquad y_i = \sum_{l=1}^{M} X_{il} \beta_l + \varepsilon_i,$$

pointwise on $\Omega$.
