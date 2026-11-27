# Almost-injective binary linear maps exist

Let $P$ be a finite set of pairs of distinct vectors in $\{0,1\}^n$ and let $A$ be a uniform $m \times n$ Boolean matrix. The expected number of pairs $(x, y) \in P$ with $Ax = Ay$ is $|P|/2^m$, so some matrix has at most $|P|/2^m$ collisions on $P$. In particular, for every $S \subseteq \{0,1\}^n$ some $A$ has at most $\binom{|S|}{2}/2^m$ colliding unordered pairs in $S$, and if $\binom{|S|}{2} < 2^m$ some linear map $\{0,1\}^n \to \{0,1\}^m$ is injective on $S$.

## Proof sketch

Each pair collides with probability $2^{-m}$ since $A(x - y)$ is uniform; linearity of expectation and averaging give the existence claims.

## Proof depends on

- [Subset-sum and random-matrix hashing are optimally Δ-universal](subset-sum-and-matrix-hashing.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979 (Proposition 9: the class $H_3$ of Boolean linear maps is universal).
