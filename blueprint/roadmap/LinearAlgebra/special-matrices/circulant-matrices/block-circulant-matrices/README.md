# Block-circulant matrices

Let $n$ and $d$ be natural numbers and let $v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}^{d \times d}$ assign a complex $d \times d$ block to each residue. The block-circulant matrix of $v$ is the complex matrix with rows and columns indexed by $\mathbb{Z}/n\mathbb{Z} \times \{0, \dots, d - 1\}$ whose $(p, q)$ block is $v(p - q)$: its entry in row $(p, a)$ and column $(q, b)$ is $v(p - q)_{ab}$.

## Idea

A block-circulant matrix is a circulant matrix whose entries are themselves $d \times d$ matrices. For $n \ge 1$ it describes a linear operator on a ring of $n$ cells, each carrying a $d$-dimensional state, that commutes with the cyclic shift of the cells. The discrete Fourier transform in the cell index block-diagonalizes it: at each frequency $j$ the operator acts by the $d \times d$ Fourier symbol $\hat v(j) = \sum_k \omega^{kj} v(k)$, with $\omega$ a primitive $n$-th root of unity, and the determinant is the product of the determinants of the symbols. The two-dimensional version on a torus $(\mathbb{Z}/L\mathbb{Z})^2$, $L \ge 1$, is used in Onsager's exact solution of the two-dimensional Ising model.

## Statements

- [Block-circulant matrix over ℤ_n](ons-block-circulant.md)
- [Two-dimensional block-circulant matrix on the torus](ons-block-circulant2-d.md): the two-dimensional version on a torus
- [Fourier symbol of a block-circulant matrix](ons-block-symbol.md): the Fourier symbol
- [Fourier symbol of a two-dimensional block-circulant matrix](ons-block-symbol2-d.md): the Fourier symbol of the two-dimensional version
