# Multi-round consistent-hashing matching on a circle

Fix independent uniformly random permutations $\sigma_1, \sigma_2, \dots$ of the discrete circle $[U' + n']$, placing balls $[U']$ and bins $[n']$ on it. Given the active balls $A$, round $i$ places the remaining balls $A_i$ and remaining bins $B_i$ on the circle by $\sigma_i$; every remaining ball whose clockwise-next occupied position is a remaining bin is matched to that bin, and both are removed. The rounds continue until no ball remains. The resulting matching depends only on $(\sigma_i)$ and $A$. This is Algorithm 1 of Li, Liang, Yu and Zhou with the bin set fixed to $[n']$ and the round hash functions taken to be uniformly random permutations, the assumption of their Claim 3.3; at most $n'$ rounds are ever needed, since each round matches at least one ball.

## Depends on

- [Memoryless dynamic matching of balls to bins](memoryless-dynamic-matching.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent Hashing and Random Trees: Distributed Caching Protocols for Relieving Hot Spots on the World Wide Web", Proceedings of the 29th ACM Symposium on Theory of Computing (STOC), pp. 654-663, 1997.
