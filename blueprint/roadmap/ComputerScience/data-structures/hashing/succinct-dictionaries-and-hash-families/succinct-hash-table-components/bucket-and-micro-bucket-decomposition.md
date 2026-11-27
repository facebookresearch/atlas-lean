# Bucket and micro-bucket address decomposition

For capacity $n \ge 1$, assign each key a bucket address of $b(n) = \lfloor \log_2 n \rfloor - \min(\lfloor \log_2 n \rfloor, 3\lambda(n))$ bits and a micro-bucket address of $\mu(n) = \min(\lfloor \log_2 n \rfloor, 3\lambda(n))$ bits, where $\lambda(n) = \Theta(\log \log n)$. Then $b(n) + \mu(n) = \lfloor \log_2 n \rfloor$, so there are exactly $2^{\lfloor \log_2 n \rfloor} \in (n/2, \max(n,1)]$ (bucket, micro-bucket) chains; each bucket indexes up to $4 \cdot 2^{\mu(n)}$ local slots with pointers of at most $\mu(n) + 3 = O(\log \log n)$ bits. Under a 3-wise independent hash, the expected number of micro-bucket collisions of a key with the other stored keys is at most $2$ and the expected overflow of its bucket above capacity is at most $1$.

## Proof sketch

The address identity is arithmetic. There are more than $n/2$ chains, so each chain has expected load less than $2$, so pairwise independence bounds the expected collisions, and the third moment controls the overflow of the bucket above four times its mean.

## Depends on

- [One-round Feistel quotienting of keys](../succinct-hash-tables/one-round-feistel-quotienting.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023.
