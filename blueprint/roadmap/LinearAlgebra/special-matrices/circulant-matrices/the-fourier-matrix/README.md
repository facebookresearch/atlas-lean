# Fourier matrix

Let $n \ge 1$ and $\zeta_n = e^{2\pi i/n}$. The Fourier matrix of order $n$ is the $n \times n$ complex matrix $F_n$, with rows and columns indexed by $\mathbb{Z}/n\mathbb{Z}$, whose entry in row $k$ and column $j$ is $\zeta_n^{kj}$, with $k$ and $j$ read as integers in $\{0, \dots, n - 1\}$.

## Idea

The columns of $F_n$ are the Fourier vectors $f_j = (\zeta_n^{kj})_k$, the characters of the cyclic group $\mathbb{Z}/n\mathbb{Z}$. They are orthogonal, each of squared length $n$, because $\sum_k \zeta_n^{k(j - j')}$ vanishes unless $j = j'$, a consequence of $\zeta_n$ being a primitive $n$-th root of unity. Hence $F_n^{-1} = \tfrac1n \overline{F_n}$, with entries $\tfrac1n \zeta_n^{-kj}$. Multiplying by $F_n^{-1}$ computes the discrete Fourier transform divided by $n$, and multiplying by $F_n$ undoes it. The matrix $F_n/\sqrt n$ is unitary, and the fast Fourier transform multiplies by $F_n$ in $O(n \log n)$ operations.

## Statements

- [Fourier matrix](fourier-matrix.md)
- [Entrywise exponential formula for the Fourier matrix](fourier-matrix-apply.md): its entries
- [Inverse Fourier matrix](fourier-matrix-inv.md): the inverse Fourier matrix
- [Entrywise exponential formula for the inverse Fourier matrix](fourier-matrix-inv-apply.md): entries of the inverse
- [Fourier matrix times its inverse is the identity](fourier-matrix-mul-inv.md): the two matrices are inverse
- [Fourier matrix acts as n times the inverse DFT](fourier-matrix-mul-vec-eq-inv-dft.md): $F_n$ acts as $n$ times the inverse discrete Fourier transform
- [Inverse Fourier matrix acts as the DFT divided by n](fourier-matrix-inv-mul-vec-eq-dft.md): $F_n^{-1}$ acts as the discrete Fourier transform divided by $n$
- [Fourier vector on the integers modulo n](fourier-vec.md): the Fourier vectors, its columns
- [Exponential formula for Fourier vectors](fourier-vec-apply.md): their entries
- [Standard primitive n-th root of unity $e^{2\pi i/n}$](zeta.md): the root of unity $\zeta_n$
- [Standard root of unity as the standard additive character](zeta-eq-std-add-char.md): $\zeta_n$ as the standard additive character
- [$e^{2\pi i/n}$ is a primitive n-th root of unity](zeta-is-primitive-root.md): $\zeta_n$ is a primitive $n$-th root of unity
