# Restricted nullspace property

A matrix $X \in \mathbb{R}^{n \times d}$ satisfies the *restricted nullspace property* over a set
$S$ of coordinates if the only vector of its nullspace in the cone
$\mathcal{C}(S; 1) = \{\Delta : \|\Delta_{S^c}\|_1 \le \|\Delta_S\|_1\}$ is $0$:

$$\mathrm{null}(X) \cap \mathcal{C}(S; 1) = \{0\}.$$

The restricted eigenvalue condition over $\mathcal{C}(S; 1)$ implies it.

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Definition 10.1.
- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §7.2.2 (exact recovery and restricted nullspace).

## Background

- [Restricted eigenvalue condition](../lasso-error-bounds-under-restricted-eigenvalues/restricted-eigenvalue.md): a quantitative strengthening, used for noisy observations.
