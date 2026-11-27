# Bootstrap of the mean in $\mathbb R^k$

Let $X_0, X_1, \dots$ be i.i.d. random vectors in $\mathbb R^k$ with $E\|X_0\|^2 < \infty$ and covariance matrix $S$. Along almost every sample sequence, as $n, m \to \infty$, the conditional law given the data of

$$\sqrt m \Bigl(\frac1m \sum_{j=1}^m X^*_j - \frac{1}{n+1} \sum_{i=0}^n X_i\Bigr)$$

converges weakly to the centred normal law with covariance $S$, where $X^*_1, \dots, X^*_m$ are drawn independently and uniformly from the data. Resampling is written through index maps as in the [one-dimensional statement](bootstrap-mean-tendsto-gaussian-real.md).

## Background

- [Mallows' contraction of normalised sums](wasserstein-two-normalized-sum-le.md): proved in any separable Hilbert space, so in $\mathbb R^k$; Bickel and Freedman refer to their Section 8 for the metrics this theorem needs.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Theorem 2.2(a).
