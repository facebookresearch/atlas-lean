# Bijective multi-level coordinate routing

In the multi-level dictionary tree, with the universe rounded up to $[U']$ by sentinel keys, the level-by-level map sending a key to its (node, identifier, quotient) coordinates at level $\ell$ is a bijection between $[U']$ and the level-$\ell$ coordinate space, the coordinates at level $\ell$ depend only on the child-router permutations of the key's ancestors at levels below $\ell$ (and of the top-level router) and on the per-child identifier permutations of the nodes on its path down to level $\ell$, and under a good seed assignment no node overflows or underflows and identifiers are injective on the active keys of each node.

## Proof sketch

Each routing step is the composition of two one-round Feistel permutations, the node's child router and the receiving child's identifier permutation (Li, Liang, Yu and Zhou, Section 5.4 and Appendix B), with fixed bit-splitting bijections, hence bijective, and the composite of bijections is bijective. The dependence claim follows by induction on the level; the load and injectivity claims are the definition of good seeds.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Proof depends on

- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
