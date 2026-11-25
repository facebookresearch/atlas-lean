# A positive-definite kernel is a positive semidefinite matrix on the whole set

If $k$ is a positive-definite kernel on $X$, the matrix $(k(x, x'))_{x, x' \in X}$ indexed by the whole set is positive semidefinite in the sense of finitely supported vectors: it is symmetric and $\sum_{x, x'} \alpha_x \alpha_{x'} k(x, x') \ge 0$ for every finitely supported $\alpha : X \to \mathbb{R}$. Proof: such a sum is the quadratic form of the kernel matrix on the support of $\alpha$.

This is the form of positive semidefiniteness used to construct the reproducing kernel Hilbert space.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 7.3, Definition 7.1; the reformulation for finitely supported vectors is derived.
