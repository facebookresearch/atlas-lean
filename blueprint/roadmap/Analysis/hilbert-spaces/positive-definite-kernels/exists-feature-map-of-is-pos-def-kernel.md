# Feature map of a positive-definite kernel

If $k$ is a positive-definite kernel on a set $X$, there are a real Hilbert space $H$ and a map $\varphi : X \to H$ such that $k(x, x') = \langle \varphi(x), \varphi(x') \rangle_H$ for all $x, x' \in X$.

The space is the reproducing kernel Hilbert space of $k$: the completion of the finite combinations $\sum_i \alpha_i k(\cdot, x_i)$ for the inner product $\langle k(\cdot, x), k(\cdot, x') \rangle = k(x, x')$, and $\varphi(x) = k(\cdot, x)$ is the kernel function at $x$. This is the reproducing kernel Hilbert space construction for positive semidefinite (operator-valued) kernels, applied to a real scalar kernel.

## Background

- [Representer theorem](../representer-theorem/README.md): background, learning in the reproducing kernel Hilbert space reduces to the span of the kernel functions at the data.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 7.3, Proposition 7.3 (the source proves this direction only partially); N. Aronszajn, Trans. Amer. Math. Soc. 68 (1950), 337–404.
