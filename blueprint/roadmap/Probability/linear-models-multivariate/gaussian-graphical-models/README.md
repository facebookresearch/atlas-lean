# Gaussian graphical models

## Mathematical overview

A Gaussian vector with positive definite covariance $\Sigma$ is described equally well by its
precision matrix $K = \Sigma^{-1}$: conditional laws and conditional independence given the other
coordinates are read off the blocks of $K$.

**Example: the Leroux conditional autoregressive (CAR) model.** Let $W$ be a symmetric matrix of nonnegative weights with zero
diagonal on a finite set of areas, $d_i = \sum_j w_{ij}$, $L = \operatorname{diag}(d) - W$,
$0 \le \rho < 1$, $v > 0$ and $Q = \rho L + (1 - \rho) I$. By
[Weighted graph Laplacians and the Leroux precision matrix](dot-product-laplacian-mul-vec-and-pos-de.md), $Q$ is positive
definite with $Q \mathbf{1} = (1 - \rho) \mathbf{1}$, so $X \sim N(\theta_0 \mathbf{1}, v Q^{-1})$ is a
proper Gaussian vector with precision $K = Q / v$.

*Conditional law of one area.* For an area $i$, the conditional covariance of $X_i$ given the
other coordinates is $(K_{ii})^{-1}$
([the conditional covariance is the inverse of a precision block](inv-to-blocks-inv.md)) and the coefficient of the conditional mean is
$-(K_{ii})^{-1} K_{i,-i}$ ([the regression coefficient from the precision matrix](to-blocks-mul-inv-to-blocks.md)). Since
$w_{ii} = 0$, we have $Q_{ii} = \rho d_i + 1 - \rho$ and $\sum_{j \ne i} w_{ij} = d_i$, so the conditional
law has mean $\bigl(\rho \sum_j w_{ij} x_j + (1 - \rho) \theta_0\bigr) / (\rho d_i + 1 - \rho)$ and
variance $v / (\rho d_i + 1 - \rho)$. The zero diagonal enters this computation, not the matrix facts.
As with every conditional distribution, the statement holds for almost every value of the other
coordinates, for a version of the conditional law. The block statements are written for a split
$\iota \sqcup \kappa$ of the index set; they apply to a single coordinate $i$ after reordering the
coordinates.

*Conditional independence.* For $i \ne j$, $K_{ij} = -\rho w_{ij} / v$. By the
[pairwise Markov property of Gaussian vectors](cond-indep-fun-iff-inv-apply-eq-zero.md), $X_i$ and $X_j$
are conditionally independent given the other coordinates if $w_{ij} = 0$, and, when
$\rho > 0$, only then. At $\rho = 0$, $Q = I$ and the coordinates are independent whatever $W$
is.

## Precision-matrix identities

- [The conditional covariance is the inverse of a precision block](inv-to-blocks-inv.md)
- [The regression coefficient from the precision matrix](to-blocks-mul-inv-to-blocks.md)
- [Partial correlation from the conditional covariance](partial-correlation.md)
- [Partial correlation from the precision matrix](partial-correlation-eq.md)
- [Weighted graph Laplacians and the Leroux precision matrix](dot-product-laplacian-mul-vec-and-pos-de.md)

## Conditional independence

- [Conditioning block of a vector](rest.md)
- [Measurability of the conditioning block](measurable-rest.md)
- [Pairwise Markov property of Gaussian vectors](cond-indep-fun-iff-inv-apply-eq-zero.md)

## Dempster's covariance selection

- [Sample second-moment matrix](sample-cov.md)
- [Sum of sample quadratic forms as a trace](sum-dot-product-mul-vec-eq.md)
- [Gaussian log-likelihood of a precision matrix](gauss-log-lik.md)
- [Matrix supported on the edges of a graph](is-supported-on.md)
- [Dempster's covariance-selection MLE](gauss-log-lik-le-of-inv-eq-on-graph.md)
- [Uniqueness of Dempster's MLE](eq-of-gauss-log-lik-eq.md)

## Related topics

- [Graph Laplacians and Cheeger's inequality](../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/README.md): weighted graph Laplacians and their quadratic forms in general.
- [Bayesian networks](../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/README.md):
  directed graphical models on finite state spaces, where conditional independence is read off
  the graph by d-separation.
