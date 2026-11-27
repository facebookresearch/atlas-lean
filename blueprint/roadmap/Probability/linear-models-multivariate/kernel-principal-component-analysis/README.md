# Kernel principal component analysis

Kernel PCA (Schölkopf, Smola and Müller 1998) is principal component analysis of the feature vectors $\Phi(x_1), \dots, \Phi(x_M)$ in a possibly infinite-dimensional feature space, computed from the kernel $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$ alone. Every eigenvector $V$ of the covariance operator $\bar C V = \frac{1}{M} \sum_j \langle \Phi(x_j), V \rangle \Phi(x_j)$ with nonzero eigenvalue $\lambda$ is an expansion $V = \sum_i \alpha_i \Phi(x_i)$, and these eigenvectors correspond to the solutions of the $M \times M$ Gram-matrix eigenproblem $M \lambda \alpha = K \alpha$; the normalisation $\|V\| = 1$ reads $M \lambda\, (\alpha \cdot \alpha) = 1$, and the principal components of a test point are $\langle V, \Phi(x) \rangle = \sum_i \alpha_i k(x_i, x)$. The same span argument is the one behind the representer theorem.

## Setting

- [Covariance operator in feature space](cov-op.md)
- [Kernel Gram matrix](gram.md)
- [The kernel Gram matrix is the Gram matrix of the feature vectors](gram-eq-matrix-gram.md)
- [The kernel PCA Gram matrix is positive semidefinite](pos-semidef-gram.md)
- [Kernel expansion in feature space](expansion.md)
- [Inner products of a kernel expansion](inner-expansion-left.md)
- [Feature vectors against a kernel expansion](inner-feature-map-expansion.md)
- [The covariance operator on kernel expansions](cov-op-expansion.md)

## Reduction to the Gram matrix

- [Eigenvectors with nonzero eigenvalue lie in the span of the data](mem-span-of-cov-op-eq-smul.md)
- [The kernel PCA eigenvalue equation in coefficient form](gram-mul-vec-eq-of-cov-op-eq-smul.md)
- [Solutions of the Gram-matrix eigenproblem are kernel principal axes](cov-op-eq-smul-of-gram-mul-vec-eq.md)
- [Every kernel principal axis comes from the Gram-matrix eigenproblem](exists-gram-mul-vec-eq-of-cov-op-eq-smul.md)

## Normalisation and projections

- [Squared norm of a kernel expansion](norm-sq-expansion.md)
- [Normalization of kernel principal axes](norm-sq-expansion-of-gram-mul-vec-eq.md)
- [Kernel PCA projections](inner-expansion-feature-map.md)

## Centring in feature space

The covariance operator is the covariance of the features only for centred features, and the mean of the features cannot be formed explicitly; the Gram matrix of the centred features is nevertheless a function of the kernel matrix.

- [Centred feature vectors](centred-feature.md)
- [The centred feature vectors are centred](sum-centred-feature.md)
- [The centred Gram matrix](gram-centred-feature.md)

## Related topics

- [Principal component analysis](../principal-component-analysis/README.md): kernel PCA is PCA of the feature vectors; with the linear kernel $k(x, y) = x^\top y$ it computes the nonzero eigenvalues of $\frac{1}{M} \sum_j x_j x_j^\top$ (for centred data, the sample covariance up to the factor $\frac{M-1}{M}$) from the $M \times M$ Gram matrix instead of the $p \times p$ matrix.
- [Representer theorem](../../../Analysis/hilbert-spaces/representer-theorem/README.md): the same argument, that the component orthogonal to the span of the data is invisible to the data, shows that regularized risk minimizers are kernel expansions.
- [Positive-definite kernels](../../../Analysis/hilbert-spaces/positive-definite-kernels/README.md): Aronszajn's theorem supplies a feature map $\Phi$ with $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$ for every positive-definite kernel, so the Gram matrix is all that kernel PCA needs.
