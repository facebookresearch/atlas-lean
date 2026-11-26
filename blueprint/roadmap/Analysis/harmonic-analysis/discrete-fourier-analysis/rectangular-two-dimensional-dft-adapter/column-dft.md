# Column DFT

For an array $y$ on $\mathbb{Z}/m \times \mathbb{Z}/n$ with $m, n \ge 1$, the column transform applies the unnormalized discrete Fourier transform $\hat f(k) = \sum_{j} e^{-2\pi i jk/N} f(j)$ on $\mathbb{Z}/N$ (with $N = m$) along the first index $i$ for each fixed second index: $(\text{column DFT } y)(k, l) = \sum_{i \in \mathbb{Z}/m} e^{-2\pi i\, i k/m}\, y(i, l)$.
