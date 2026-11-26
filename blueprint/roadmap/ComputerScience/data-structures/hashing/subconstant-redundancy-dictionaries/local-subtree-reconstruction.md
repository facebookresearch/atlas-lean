# Local subtree reconstruction in the dictionary tree

In the multi-level dictionary tree, given replacement seeds that agree with the current seeds outside the subtree of a node $u$ at level $\ell_0$ and are good on the current key set, rebuilding the subtree of $u$ canonically and splicing it in changes only that subtree and the metadata of the $\ell_0 - 1$ strict ancestors of $u$; all other subtrees and root trees are unchanged, and the represented dictionary is unchanged.

## Proof sketch

Canonical construction is a function of the subtree's keys and seeds, and the ancestors' metadata depends on the subtree only through its sizes, which the splice updates.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Proof depends on

- [Existence of good seed assignments for the dictionary tree](good-seed-existence.md)
- [Bijective multi-level coordinate routing](bijective-multi-level-routing.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
