# Inverse Fourier matrix

Let $n \ge 1$, let $\zeta_n = e^{2\pi i/n}$, and let $\psi_n$ be the standard additive character of
$\mathbb{Z}/n\mathbb{Z}$. The inverse Fourier matrix of order $n$ is the $n \times n$ complex
matrix, with rows and columns indexed by $\mathbb{Z}/n\mathbb{Z}$, whose entry in row $k$ and
column $j$ is $\frac{1}{n} \psi_n(-kj) = \frac{1}{n} \zeta_n^{-kj}$, with $k$ and $j$ read as
integers in $\{0, \dots, n-1\}$. It is the inverse of the [Fourier matrix](fourier-matrix.md).
