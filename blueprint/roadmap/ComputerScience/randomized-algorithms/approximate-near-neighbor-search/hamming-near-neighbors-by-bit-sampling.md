# Approximate near neighbours in Hamming space by bit sampling

On $\{0, 1\}^d$ with Hamming distance, sampling a uniformly random coordinate is an $(r, cr, 1 - r/d, 1 - cr/d)$-sensitive family for $c r < d$. Its exponent satisfies $\rho \le 1/c$, and the LSH index on $n$ points with standard parameters uses $L < n^{1/c} / (1 - r/d) + 1$ tables and fails with probability at most $e^{-1} + 1/3$ on every query having a point within distance $r$.

## Proof sketch

Two words at distance $\delta$ agree on a random coordinate with probability $1 - \delta/d$, which is monotone in $\delta$. The exponent bound is the concavity lemma with $a = r/d$, and the failure bound is the general LSH bound.

## Depends on

- [Locality-sensitive hashing index with L tables and a stopping rule](lsh-index.md)

## Proof depends on

- [LSH exponent bound rho at most 1/c for linear collision profiles](lsh-exponent-bound.md)
- [Failure probability of the LSH index](failure-probability-of-the-lsh-index.md)

## Sources

- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing (STOC), 1998.
- S. Har-Peled, P. Indyk and R. Motwani, "Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality", Theory of Computing 8(14), 2012.
