# Inner products of features form a positive-definite kernel

If $\varphi : X \to H$ is any map into a real inner product space, the kernel $k(x, x') = \langle \varphi(x), \varphi(x') \rangle$ is positive definite: each kernel matrix is the Gram matrix of the vectors $\varphi(x_i)$, and $\alpha^\top K \alpha = \|\sum_i \alpha_i \varphi(x_i)\|^2 \ge 0$.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 7.3, proof of Proposition 7.3 (the direction proved there).
