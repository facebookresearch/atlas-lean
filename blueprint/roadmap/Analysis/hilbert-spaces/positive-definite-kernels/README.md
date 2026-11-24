# Positive-definite kernels

A real function $k$ on $X \times X$ is a positive-definite kernel when every kernel matrix $(k(x_i, x_j))_{i,j}$ is symmetric positive semidefinite. Aronszajn's theorem identifies these kernels with inner products of features, $k(x, x') = \langle \varphi(x), \varphi(x') \rangle$, the feature space being the reproducing kernel Hilbert space of $k$; this is the basis of kernel methods in machine learning.

- [Positive-definite kernel](is-pos-def-kernel.md)
- [Aronszajn's theorem](is-pos-def-kernel-iff-exists-feature-map.md)
- [Feature map of a positive-definite kernel](exists-feature-map-of-is-pos-def-kernel.md)
- [Inner products of features form a positive-definite kernel](is-pos-def-kernel-of-eq-inner.md)
- [A positive-definite kernel is a positive semidefinite matrix on the whole set](pos-semidef-of-is-pos-def-kernel.md)

## Related topics

- [Representer theorem](../representer-theorem/README.md): empirical risk minimization in the reproducing kernel Hilbert space, and kernel ridge regression.
- [Generalization bounds and concentration](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/README.md): the dimension-free Rademacher average of balls of the feature space.
- [Two-layer neural networks and Barron space](../../../ComputerScience/machine-learning/supervised-learning/two-layer-neural-networks-and-barron-space/README.md): kernel and random-feature models fix the inner weights of a two-layer network; E, Ma and Wu describe the Barron space as the union of the reproducing kernel Hilbert spaces of the kernels $k_\pi(x, x') = \mathbb{E}_{w \sim \pi} \sigma(\langle w, x \rangle) \sigma(\langle w, x' \rangle)$ over all weight distributions $\pi$.
- [Random Fourier features](../../../ComputerScience/machine-learning/supervised-learning/random-fourier-features/README.md): randomized finite-dimensional feature maps whose inner products are unbiased estimates of a shift-invariant kernel.
- [Kernel mean embeddings and maximum mean discrepancy](../../../Probability/convergence-of-measures/kernel-mean-embeddings-and-maximum-mean-discrepa/README.md): the feature map embeds probability measures, $P \mapsto \mathbb{E}_P\, k(\cdot, x)$, and the RKHS distance of embeddings is the maximum mean discrepancy.
- [Kernel principal component analysis](../../../Probability/linear-models-multivariate/kernel-principal-component-analysis/README.md): principal component analysis of the features, computed from the kernel matrix alone.
