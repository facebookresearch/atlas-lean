# Rectangular convolution theorem

Let $m, n > 0$ and consider arrays $x : \mathbb{Z}/m \times \mathbb{Z}/n \to \mathbb{C}$. The one-dimensional DFT on $\mathbb{Z}/N$ is $\hat x(k) = \sum_{j} e^{-2\pi i jk/N} x(j)$ with inverse $\check X(j) = \frac1N \sum_k e^{2\pi i jk/N} X(k)$. The row-then-column DFT $\mathcal F x$ applies the DFT along the second index for each fixed first index, then along the first index for each fixed second index. The rectangular inverse DFT $\mathcal F^{-1}$ applies the inverse DFT along the first index, then along the second. For all arrays $x, y$,

$$\mathcal F^{-1}\big(\mathcal F x \cdot \mathcal F y\big)(s, t) = \sum_{i \in \mathbb{Z}/m} \sum_{j \in \mathbb{Z}/n} x(i, j)\, y(s - i, t - j),$$

where the product is pointwise and indices are taken modulo $m$ and $n$.
