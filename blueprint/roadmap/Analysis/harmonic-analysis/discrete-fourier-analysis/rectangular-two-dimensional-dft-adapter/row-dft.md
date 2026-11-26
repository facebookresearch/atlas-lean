# Row DFT

For an array $x$ on $\mathbb{Z}/m \times \mathbb{Z}/n$ with $m, n \ge 1$, the row transform applies the unnormalized discrete Fourier transform $\hat f(k) = \sum_{j} e^{-2\pi i jk/N} f(j)$ on $\mathbb{Z}/N$ (with $N = n$) along the second index $j$ for each fixed first index: $(\text{row DFT } x)(i, l) = \sum_{j \in \mathbb{Z}/n} e^{-2\pi i\, j l/n}\, x(i, j)$.
