# Fourier matrix

Let $n \ge 1$ and $\zeta_n = e^{2\pi i/n}$. The Fourier matrix of order $n$ is the $n \times n$
complex matrix $F_n$, with rows and columns indexed by $\mathbb{Z}/n\mathbb{Z}$, whose $j$-th
column is the [Fourier vector](fourier-vec.md) $f_j$: its entry in row $k$ and column $j$ is
$\psi_n(kj) = \zeta_n^{kj}$, where $\psi_n$ is the standard additive character of
$\mathbb{Z}/n\mathbb{Z}$ and $k$, $j$ are read as integers in $\{0, \dots, n-1\}$.
