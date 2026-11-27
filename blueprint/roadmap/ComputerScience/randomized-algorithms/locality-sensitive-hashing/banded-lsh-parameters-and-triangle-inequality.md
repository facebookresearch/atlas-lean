# Banded LSH parameters and Charikar's triangle inequality

Let a hash family be $(p_1, p_2)$-sensitive for relations near/far with $0 \le p_2 < p_1 \le 1$, and let $s(p) = 1 - (1 - p^k)^L$ be the collision probability of $L$ bands of $k$ independent rows. Then $1 - \delta \le s(p)$ whenever $\log(1/\delta) \le Lp^k$, and $s(p) \le Lp^k$ always. Consequently for all $\delta, \delta' > 0$ there are $k$ and $L = \lceil\log(1/\delta)/p_1^k\rceil$ such that near pairs collide with probability at least $1 - \delta$ and far pairs with probability at most $\delta'$. Moreover (Charikar) for any keyed family, with seeds drawn from any probability measure and measurable collision events, $d(x, y) = 1 - \Pr[h(x) = h(y)]$ satisfies the triangle inequality $d(x, z) \le d(x, y) + d(y, z)$; for MinHash this is the triangle inequality for Jaccard distance.

## Proof sketch

$(1 - p^k)^L \le e^{-Lp^k} \le \delta$ gives the near bound, and a union bound over bands gives $s(p) \le Lp^k$. Since $p_2/p_1 < 1$, $Lp_2^k \approx \log(1/\delta)(p_2/p_1)^k \to 0$ as $k$ grows. The triangle inequality follows from $\{h(x) \ne h(z)\} \subseteq \{h(x) \ne h(y)\} \cup \{h(y) \ne h(z)\}$.

## Depends on

- [Locality-sensitive hash families](locality-sensitive-hash-families.md)
- [Amplification of locality-sensitive families by banding](amplification-of-locality-sensitive-families-by.md)
- [MinHash collision probability](../minhash-and-jaccard-similarity/uniform-on-min-hash-collision.md)

## Proof depends on

- [Amplification of locality-sensitive families by banding](amplification-of-locality-sensitive-families-by.md)

## Sources

- M. S. Charikar, "Similarity Estimation Techniques from Rounding Algorithms", Proceedings of the 34th ACM Symposium on Theory of Computing, 2002.
- J. Leskovec, A. Rajaraman and J. D. Ullman, "Mining of Massive Datasets", Cambridge University Press, 2020.
- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing, 1998.
