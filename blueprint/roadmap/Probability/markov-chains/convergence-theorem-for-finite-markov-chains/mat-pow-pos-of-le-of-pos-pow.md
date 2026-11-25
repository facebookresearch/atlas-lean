# Later powers of a positive stochastic matrix power stay positive

Let $P$ be a [stochastic matrix](../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)
on the states $\{0, \dots, M\}$ and $w \le m$ natural numbers. If every entry of the [matrix
power](../kolmogorov-s-criterion-for-reversibility/mat-pow.md) $P^w$ is strictly positive, then so
is every entry of $P^m$.

Indeed $P^m(i, j) = \sum_k P^{m-w}(i, k) P^w(k, j)$; row $i$ of $P^{m-w}$ is nonnegative and sums
to $1$, so some entry $P^{m-w}(i, k)$ is positive, and its product with $P^w(k, j) > 0$ is a
positive summand.
