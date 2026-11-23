# Regularized covariance estimation by banding

When the dimension $p$ is comparable to or larger than the sample size $n$, the sample covariance matrix is a poor estimator of the population covariance in operator norm. Bickel and Levina (2008) regularize it by *banding*, keeping only the entries within distance $k$ of the diagonal, which suits variables with a natural order whose dependence decays with distance, as in time series, climatology and spectroscopy. Over the class of well-conditioned covariances with polynomially decaying off-band column sums, the banded sample covariance and its inverse are consistent in operator norm whenever $\log p / n \to 0$, at an explicit rate. The deterministic operator-norm bounds behind the rate follow from Schur's test.

- [Banding operator](band.md)
- [Banding is linear](band-sub.md)
- [The bandable class $\mathcal U(\varepsilon_0, \alpha, C)$](bandable-class.md)
- [Bias of banding](norm-band-sub-le.md)
- [Uniform bias bound on the bandable class](norm-band-sub-le-of-mem-bandable-class.md)
- [Operator norm of a banded matrix](norm-band-le.md)
- [Bickel–Levina rate for the banded sample covariance](banded-sample-covariance-rate.md)

## Related topics

- [Principal component analysis](../principal-component-analysis/README.md): eigenvalues and eigenvectors of the sample covariance, which operator-norm consistency controls.
- [Gaussian graphical models](../gaussian-graphical-models/README.md): structure in the inverse covariance, the other natural target of regularization.
- [Matrix concentration inequalities](../../concentration-inequalities/matrix-concentration-inequalities/README.md): operator-norm deviation bounds for sums of random matrices.
- [Sub-exponential variables and Bernstein's inequality](../../concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/README.md): the entrywise tail bounds used in the union bound.
- [Operator norm of random matrices](../../high-dimensional-probability/operator-norm-of-random-matrices/README.md): the spectral norm of unstructured random matrices, the regime where the sample covariance fails.
- [Schur test](../../../Analysis/operator-theory/integral-and-multiplication/schur-test/README.md): the operator-norm bound by row and column sums.
