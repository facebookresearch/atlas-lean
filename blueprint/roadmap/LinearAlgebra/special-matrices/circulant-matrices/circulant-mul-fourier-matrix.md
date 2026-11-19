# Circulant matrices are diagonalized by the Fourier matrix

Let $n \ge 1$, let $v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$, and let $C(v)$ be the circulant
matrix whose entry in row $k$ and column $l$ is $v(k - l)$. Then

$$C(v)\, F_n = F_n \operatorname{diag}\bigl(\lambda_j(v)\bigr)_{j \in \mathbb{Z}/n\mathbb{Z}},$$

where $F_n$ is the [Fourier matrix](fourier-matrix.md) and
$\lambda_j(v) = \sum_k v(k)\, \zeta_n^{-kj}$ are the [Fourier eigenvalues](circulant-eigenvalue.md),
$\zeta_n = e^{2\pi i/n}$. Since $F_n$ is invertible, every circulant matrix is diagonalized by the
Fourier matrix.
