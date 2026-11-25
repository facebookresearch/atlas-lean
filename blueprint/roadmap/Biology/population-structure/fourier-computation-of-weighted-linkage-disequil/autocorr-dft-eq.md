# Zero-padded circular autocorrelation equals linear autocorrelation

Let $N \ge 1$ and $K$ be natural numbers with $2K \le N + 1$, and let $U$ be a real sequence with $U_k = 0$ for every $k \ge K$. Then for every $j < K$,

$$\mathrm{AC}_N(U)(j) = \sum_{k=0}^{K-1} U_k\, U_{k+j},$$

where $\mathrm{AC}_N$ is the [autocorrelation via the discrete Fourier transform](autocorr-dft.md).
