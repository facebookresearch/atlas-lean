# Bucket-load concentration for Feistel routing

Route keys $x = (x_L, x_R)$ to buckets by the left half of the one-round Feistel image, $x \mapsto x_L \oplus f(x_R)$, with the round function $f$ drawn from a $k$-wise independent family. Then distinct keys with the same right half go to distinct buckets, each key is recovered from its bucket and right half, and for every set of $n$ keys and every bucket the load deviates from its mean $\mu$ by more than $t$ with probability at most $O\left((k \mu / t^2)^{k/2}\right)$ (a $k$-th moment bound); for router seeds of suitable size this gives concentration of all child loads simultaneously with probability $1 - o(1)$.

## Proof sketch

Keys sharing a right half are mapped by a fixed exclusive or, which is injective. The load of a bucket is a sum of indicators that are $k$-wise independent over the distinct right halves, so the $k$-th central moment bound and Markov's inequality give the tail.

## Depends on

- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
