# Local subtree reconstruction in the dictionary tree

In the multi-level dictionary tree, *rehashing* a node $u$ at level $\ell_0$ (Li, Liang, Yu and Zhou, Algorithm 4) samples fresh hash functions for $u$, resampling until they do not fail on the keys received by $u$, distributes those keys to the children of $u$, rehashes every child recursively, and then fills the storage table (or minimap) and, if $u$ is not a root, the waiting list of $u$. The set of keys received by $u$ is determined by the hash functions of the strict ancestors of $u$, so it is unchanged; the rebuilt subtree again stores exactly $\underline{n}_{\ell_0}$ keys when $u$ is not a root, so every fixed-size structure outside the subtree of $u$ keeps its size and position, and the represented dictionary is unchanged. Rehashing the subtree of $u$ takes $O(n_{\ell_0} (k - \ell_0 + 1))$ expected time. The source describes this step only as reconstructing the subtree rooted at $u$; it does not spell out how the keys returned by $u$ are re-stored at its ancestors.

## Proof sketch

Routing is bijective and level by level, so resampling the hash functions of $u$ changes only the routing inside the subtree of $u$. Each level-$\ell$ node of the subtree is processed in $O(n_\ell)$ expected time, including the expected number of resamplings, which is $O(1)$ because a fresh seed fails with probability at most $3/n_\ell^2$; summing over the $k - \ell_0 + 1$ levels of the subtree gives the time bound (Section 5.5).

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Proof depends on

- [Existence of good seed assignments for the dictionary tree](good-seed-existence.md)
- [Bijective multi-level coordinate routing](bijective-multi-level-routing.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
