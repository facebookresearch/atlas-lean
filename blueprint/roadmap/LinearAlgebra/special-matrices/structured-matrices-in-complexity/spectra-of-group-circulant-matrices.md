# Spectra of group-circulant matrices and Boolean-cube diagonalization

Let $G$ be a finite abelian group and $w:G\to\mathbb{C}$. The group-circulant matrix $C_w=(w(x-y))_{x,y\in G}$ has every character $\psi$ of $G$ as an eigenvector with eigenvalue $\hat w(\psi)=\sum_{g\in G}w(g)\overline{\psi(g)}$, and $C_wC_{w'}=C_{w\ast w'}$ with $\widehat{w\ast w'}=\hat w\,\hat w'$. For $G=\mathbb{F}_2^n$ the characters are the Walsh functions, so every group-circulant matrix on the Boolean cube is diagonalized by the Sylvester–Hadamard matrix, the eigenvalue at the Walsh function $\chi_S$ being $\sum_{g}w(g)\chi_S(g)$; for real $w$ this is $2^n\hat w(S)$, where $\hat w(S)=2^{-n}\sum_{g}w(g)\chi_S(g)$ is the normalized Fourier coefficient.

## Proof sketch

$(C_w\psi)(x)=\sum_yw(x-y)\psi(y)=\psi(x)\sum_gw(g)\psi(-g)$ by substituting $g=x-y$; convolution corresponds to products of eigenvalues by orthogonality of characters.

## Depends on

- [Fourier eigenvalue of a circulant matrix](../circulant-matrices/eigenvalues-of-circulant-matrices/circulant-eigenvalue.md)
- [Hadamard matrix](../hadamard-matrices/is-hadamard-matrix.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
