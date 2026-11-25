# Inverse FFT at the negative-sign root computes the inverse DFT

Let $N = 2^d$ and
$x \in \mathbb{C}^N$, and run the inverse FFT procedure on $x$ with root $e^{-2\pi i/N}$, the value
at $-1$ of the standard additive character of $\mathbb{Z}/N\mathbb{Z}$. For every $k < N$, entry $k$
of its output equals the canonical inverse discrete Fourier transform of the function on
$\mathbb{Z}/N\mathbb{Z}$ sending the class of $j < N$ to $x_j$, evaluated at the class of $k$;
that is, it equals $N^{-1} \sum_{j=0}^{N-1} e^{2\pi i jk/N} x_j$.
