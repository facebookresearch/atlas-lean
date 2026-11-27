# Uncentred second-moment matrix of a data matrix

Let $X$ be a real $n \times p$ data matrix whose rows $x_1, \dots, x_n$ are the samples. Its
uncentred second-moment matrix is the $p \times p$ matrix

$$\frac1n X^\top X, \qquad \Bigl(\frac1n X^\top X\Bigr)_{jk} = \frac1n \sum_{i=1}^n X_{ij} X_{ik}.$$

For $n \ge 1$ it is the second-moment matrix $\frac1n \sum_i x_i x_i^\top$ of the empirical
distribution of the samples. For $n = 0$ it is the zero matrix.
