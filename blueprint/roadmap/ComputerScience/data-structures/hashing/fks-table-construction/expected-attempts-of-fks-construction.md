# Expected attempts of the FKS perfect-hashing construction

Let $F$ be a family of 2-universal hash functions available for every range size, and let $X$ be a set of $n$ keys. The randomized FKS construction draws top-level functions $h_0 : X \to [n]$ until the bucket sizes $b_j = |h_0^{-1}(j)|$ satisfy $\sum_j b_j^2 \le 4n$, and then, for each bucket $j$, draws functions $g_j : h_0^{-1}(j) \to [b_j^2]$ until $g_j$ is injective on the bucket. Each top-level attempt and each bucket attempt succeeds with probability at least $1/2$, so each level takes at most $2$ attempts in expectation, and the expected total number of draws and hash evaluations is $O(n)$. The resulting table occupies at most $6n + 1$ cells (at most $4n$ second-level cells, one seed and one address for each of the $n$ buckets, and one top-level seed) and answers membership with a constant number of cell reads.

## Proof sketch

By 2-universality the expected number of colliding pairs at the top level is at most $\binom{n}{2}/n$, so $\mathbb{E}\sum_j b_j^2 \le 2n$ and Markov's inequality gives success probability at least $1/2$. For a bucket of $b$ keys hashed into $b^2$ cells the expected number of collisions is at most $\binom{b}{2}/b^2 < 1/2$. Expected attempts of a geometric trial with success probability at least $1/2$ are at most $2$.

## Depends on

- [Two-level perfect hash table](../perfect-hashing/perfect-hashing.md)
- [Universal hash family](../universal-hashing/is-universal.md)

## Proof depends on

- [Two-level perfect hashing uses linear expected space](../hashing-analysis/two-level-perfect-hashing-uses-linear-expected-space.md)

## Sources

- M. L. Fredman, J. Komlos and E. Szemeredi, "Storing a Sparse Table with O(1) Worst Case Access Time", Journal of the ACM 31(3), 1984.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
