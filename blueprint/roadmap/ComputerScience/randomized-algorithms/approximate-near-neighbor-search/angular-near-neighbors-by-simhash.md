# Approximate near neighbours in angular distance by SimHash

On nonzero vectors of a real inner-product space with angular distance $\theta(x, y) \in [0, \pi]$, SimHash ($x \mapsto \mathrm{sign}\langle g, x \rangle$ for a standard Gaussian vector $g$) collides with probability $1 - \theta(x,y)/\pi$ and is therefore $(\theta, c\theta, 1 - \theta/\pi, 1 - c\theta/\pi)$-sensitive for $0 < \theta$, $1 < c$, $c\theta < \pi$. Its exponent satisfies $\rho \le 1/c$, and the LSH index with $L < n^{1/c}/(1 - \theta/\pi) + 1$ AND-composed SimHash tables answers $(c, \theta)$-approximate angular near-neighbour queries with failure probability at most $e^{-1} + 1/3$.

## Proof sketch

The hyperplane orthogonal to $g$ separates $x$ and $y$ exactly when $g$ falls in a wedge of angle $2\theta(x,y)$ out of $2\pi$, by rotational invariance of the Gaussian in the plane spanned by $x$ and $y$. The exponent bound is the concavity lemma with $a = \theta/\pi$.

## Depends on

- [Locality-sensitive hashing index with L tables and a stopping rule](lsh-index.md)

## Proof depends on

- [LSH exponent bound rho at most 1/c for linear collision profiles](lsh-exponent-bound.md)
- [Failure probability of the LSH index](failure-probability-of-the-lsh-index.md)

## Sources

- M. S. Charikar, "Similarity Estimation Techniques from Rounding Algorithms", Proceedings of the 34th ACM Symposium on Theory of Computing (STOC), 2002.
- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing (STOC), 1998.
