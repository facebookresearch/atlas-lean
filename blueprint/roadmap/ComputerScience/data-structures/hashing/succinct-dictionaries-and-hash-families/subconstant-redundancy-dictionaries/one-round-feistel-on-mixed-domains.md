# One-round Feistel permutations on mixed domains

For a round function $f : \mathcal{R} \to [2^s]$, the one-round Feistel map on $[2^s] \times \mathcal{R}$ is $(x_L, x_R) \mapsto (x_L \oplus f(x_R), x_R)$; it is an involution, hence a permutation. Identifying $[2^s T]$ with $[2^s] \times [T]$ by $u \mapsto (u \bmod 2^s, \lfloor u / 2^s \rfloor)$ turns it into a permutation of $[2^s T]$ for every $T$, which allows key-ID compression and routing of keys to child nodes in a multi-level dictionary without assuming the universe size is a power of two. Drawing $f$ from a family of hash functions yields a family of permutations (Li, Liang, Yu and Zhou, Definition B.1 and Corollaries B.5 and B.6). Luby and Rackoff study Feistel networks with pseudorandom round functions; only the permutation property of a single round is used here.

## Depends on

- [One-round Feistel quotienting of keys](../succinct-hash-tables/one-round-feistel-quotienting.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing 17(2), pp. 373-386, 1988.
- M. Naor and O. Reingold, "On the Construction of Pseudorandom Permutations: Luby-Rackoff Revisited", Journal of Cryptology 12(1), pp. 29-66, 1999.
