# Row-then-column DFT equals the two-dimensional DFT sum

Let $m, n > 0$ and consider arrays $x : \mathbb{Z}/m \times \mathbb{Z}/n \to \mathbb{C}$. The one-dimensional DFT on $\mathbb{Z}/N$ is $\hat x(k) = \sum_{j} e^{-2\pi i jk/N} x(j)$ with inverse $\check X(j) = \frac1N \sum_k e^{2\pi i jk/N} X(k)$. The row-then-column DFT $\mathcal F x$ applies the DFT along the second index for each fixed first index, then along the first index for each fixed second index. Then for every array $x$ and every $(k, l)$,
$$\mathcal F x(k, l) = \sum_{i \in \mathbb{Z}/m} \sum_{j \in \mathbb{Z}/n} \exp\!\left(-2\pi i \left(\frac{i k}{m} + \frac{j l}{n}\right)\right) x(i, j),$$
with $i, j, k, l$ read as their representatives in $\{0, \dots, m-1\}$ and $\{0, \dots, n-1\}$.
