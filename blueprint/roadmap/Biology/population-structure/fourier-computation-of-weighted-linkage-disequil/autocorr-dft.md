# Autocorrelation via the discrete Fourier transform

For a natural number $N \ge 1$, a real sequence $U$ and $j \in \mathbb{N}$, put

$$\mathrm{AC}_N(U)(j) = \mathcal{F}^{-1}\bigl(|\mathcal{F} \tilde U|^2\bigr)(j \bmod N),$$

where $\tilde U$ is the [zero-padded sequence](pad.md), $\mathcal{F}\Phi(\xi) = \sum_{k \in \mathbb{Z}/N} e^{-2\pi i k \xi / N}\, \Phi(k)$ is the discrete Fourier transform on $\mathbb{Z}/N\mathbb{Z}$ and $\mathcal{F}^{-1}\Psi(k) = \frac{1}{N} \sum_{\xi} e^{2\pi i k \xi / N}\, \Psi(\xi)$ its inverse: the inverse transform of the power spectrum, read at $j$.
