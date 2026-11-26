# Inverse row DFT

For an array $X$ on $\mathbb{Z}/m \times \mathbb{Z}/n$ with $m, n \ge 1$, the inverse row transform applies the inverse discrete Fourier transform $\check F(j) = \frac{1}{N}\sum_{k} e^{2\pi i jk/N} F(k)$ on $\mathbb{Z}/N$ (with $N = n$) along the second index for each fixed first index.
