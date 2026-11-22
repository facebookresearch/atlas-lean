# The array FFT computes the discrete Fourier transform

Let $d$ be a natural number,
$\omega \in \mathbb{C}$ a primitive $2^d$-th root of unity, $x_0, \dots, x_{2^d - 1}$ complex
numbers and $k < 2^d$. Then the array FFT of the array $(x_0, \dots, x_{2^d - 1})$ with root
$\omega$ returns an array $y$ of length $2^d$ whose entry at index $k$ is the discrete Fourier
sum $\sum_{j=0}^{2^d - 1} \omega^{jk} x_j$.
