# Fourier vectors are eigenvectors of circulant matrices

Let $n \ge 1$, let $v : \mathbb{Z}/n\mathbb{Z} \to \mathbb{C}$, and let $C(v)$ be the circulant
matrix whose entry in row $k$ and column $l$ is $v(k - l)$. For every $j \in \mathbb{Z}/n\mathbb{Z}$,
the [Fourier vector](../the-fourier-matrix/fourier-vec.md) $f_j$ satisfies $C(v) f_j = \lambda_j(v) f_j$, where
$\lambda_j(v) = \sum_k v(k)\, \zeta_n^{-kj}$ is the [Fourier eigenvalue](circulant-eigenvalue.md)
and $\zeta_n = e^{2\pi i/n}$. Since $f_j$ has entries of modulus $1$, it is an eigenvector.
