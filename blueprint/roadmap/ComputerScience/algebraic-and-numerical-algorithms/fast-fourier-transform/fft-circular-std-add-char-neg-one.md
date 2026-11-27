# FFT circular convolution with root $e^{-2\pi i/n}$ computes the cyclic convolution

Let
$n = 2^d$ and $x, y \in \mathbb{C}^n$. Run FFT circular convolution of $x$ and $y$ with root
$\omega = e^{-2\pi i/n}$, the value at $-1$ of the standard additive character of
$\mathbb{Z}/n\mathbb{Z}$. Then for every $k < n$, entry $k$ of the returned vector equals
$\sum_{j \in \mathbb{Z}/n\mathbb{Z}} x_j \, y_{k - j}$, with indices taken modulo $n$.

This root is the sign convention of the Princeton (Sedgewick–Wayne) source.
