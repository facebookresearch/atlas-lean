# Positive-definite kernel

A function $k : X \times X \to \mathbb{R}$ on an arbitrary set $X$ is a positive-definite kernel if for every $n$ and all points $x_1, \dots, x_n \in X$ the kernel matrix $K = (k(x_i, x_j))_{i,j}$ is symmetric positive semidefinite: $K^\top = K$ and $\alpha^\top K \alpha = \sum_{i,j} \alpha_i \alpha_j k(x_i, x_j) \ge 0$ for all $\alpha \in \mathbb{R}^n$.

No structure is assumed on $X$: kernels can be defined on sequences, graphs, distributions or any other inputs, which is what makes kernel methods applicable beyond vector data.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 7.3, Definition 7.1.
