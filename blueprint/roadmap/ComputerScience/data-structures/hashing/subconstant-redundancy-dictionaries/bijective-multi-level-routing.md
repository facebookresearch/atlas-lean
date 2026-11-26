# Bijective multi-level coordinate routing

In the multi-level dictionary tree, pad the key universe with sentinel keys so that every level's coordinate space has the exact size required by the schedule. Then the level-by-level map sending a key to its (node, identifier, quotient) coordinates at level $\ell$ is a bijection between the padded universe and the level-$\ell$ coordinate space, the coordinates at level $\ell$ depend only on the seeds of the key's ancestors at levels below $\ell$, and under a seed assignment in which every node is good, node loads stay within capacity and identifiers are injective on the active keys of each node.

## Proof sketch

Each routing step is the composition of a one-round Feistel permutation with a fixed mixed-radix bijection, hence bijective, and the composite of bijections is bijective. The dependence claim follows by induction on the level; the load and injectivity claims are the definition of good seeds.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Proof depends on

- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
