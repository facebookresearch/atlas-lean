# Aronszajn's theorem

A function $k : X \times X \to \mathbb{R}$ on an arbitrary set $X$ is a positive-definite kernel if and only if there are a real Hilbert space $H$ and a map $\varphi : X \to H$ with

$$
k(x, x') = \langle \varphi(x), \varphi(x') \rangle_H \quad \text{for all } x, x' \in X.
$$

The two directions are the Gram-matrix argument and the construction of the reproducing kernel Hilbert space of $k$. In learning, this is what allows linear methods in an implicit, possibly infinite-dimensional, feature space to be run with kernel evaluations only (the "kernel trick"), and it places kernel methods inside the theory of linear predictors with norm constraints.

## Background

- [Rademacher average of a ball of linear predictors](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/rademacher-average-linear-ball-le.md): background, the dimension-free complexity bound that applies to balls of the feature space.
- [Kernel ridge regression](../representer-theorem/kernel-ridge-risk-kernel-ridge-fit-le.md): background, the estimator computed in the reproducing kernel Hilbert space.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 7.3, Proposition 7.3; N. Aronszajn, Trans. Amer. Math. Soc. 68 (1950), 337–404.
