# Circulant matrices are diagonalized by the Fourier matrix

Let $n \ge 1$, let $v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$, and let $C(v)$ be the circulant matrix with entry $v(k - l)$ in row $k$ and column $l$. Then

$$C(v)\, F_n = F_n \operatorname{diag}\bigl(\lambda_j(v)\bigr)_{j \in \mathbb{Z}/n\mathbb{Z}},$$

where $F_n = (\zeta_n^{kj})_{k, j}$ is the Fourier matrix, $\zeta_n = e^{2\pi i/n}$, and $\lambda_j(v) = \sum_k v(k)\, \zeta_n^{-kj}$.

## Idea

A circulant matrix is the matrix of a convolution on $\mathbb{Z}/n\mathbb{Z}$: each row is the previous one shifted cyclically. Convolutions commute with cyclic shifts, and the common eigenvectors of all shifts are the Fourier vectors $f_j = (\zeta_n^{kj})_k$. Since $F_n$ is invertible, the identity above says that every circulant matrix is diagonal in the Fourier basis, with eigenvalues given by the discrete Fourier transform of its first column. Consequences are immediate: $\det C(v) = \prod_j \lambda_j(v)$, $\lambda_0(v)$ is the sum of the entries, and products of circulant matrices, and inverses of invertible ones, are circulant. This is why convolutions are computed with the fast Fourier transform.

## Statements

- [Circulant matrices are diagonalized by the Fourier matrix](circulant-mul-fourier-matrix.md)
- [Fourier eigenvalue of a circulant matrix](circulant-eigenvalue.md): the eigenvalues $\lambda_j(v)$
- [Fourier vectors are eigenvectors of circulant matrices](circulant-mul-vec-fourier-vec.md): each Fourier vector is an eigenvector
- [Exponential-sum formula for circulant eigenvalues](circulant-eigenvalue-apply.md): the exponential-sum formula for $\lambda_j(v)$
- [Zeroth circulant eigenvalue is the sum of entries](circulant-eigenvalue-zero.md): $\lambda_0(v)$ is the sum of the entries
- [Sum of the eigenvalues of a circulant matrix](sum-circulant-eigenvalue.md): the eigenvalues sum to $n\,v(0)$
- [Determinant of a circulant matrix](det-circulant.md): consequence: the determinant is the product of the eigenvalues
