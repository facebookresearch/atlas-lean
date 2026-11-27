# Recursive matrix power agrees with the matrix power

Let $P$ be a [stochastic matrix](../kolmogorov-s-criterion-for-reversibility/stochastic-matrix.md)
on the states $\{0, \dots, M\}$. The recursively defined [powers](../kolmogorov-s-criterion-for-reversibility/mat-pow.md)
$P^0 = I$, $P^{n+1}(i, j) = \sum_k P(i, k) P^n(k, j)$ agree entrywise with the ordinary powers of
its [underlying real matrix](to-matrix.md), for every $n \in \mathbb{N}$.
