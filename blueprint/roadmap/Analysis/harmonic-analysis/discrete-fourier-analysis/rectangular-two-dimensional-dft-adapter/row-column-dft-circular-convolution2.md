# The two-dimensional DFT turns circular convolution into a product

For $m, n \ge 1$ and arrays $x, y$ on $\mathbb{Z}/m \times \mathbb{Z}/n$, let $(x * y)(p, q) = \sum_{i, j} x(i, j)\, y(p - i, q - j)$ be the two-dimensional circular convolution (indices mod $m$ and mod $n$). The row-then-column DFT $\mathcal F$ (unnormalized, negative exponent) turns it into a pointwise product: $\mathcal F(x * y)(k, l) = \mathcal F x(k, l)\, \mathcal F y(k, l)$.
