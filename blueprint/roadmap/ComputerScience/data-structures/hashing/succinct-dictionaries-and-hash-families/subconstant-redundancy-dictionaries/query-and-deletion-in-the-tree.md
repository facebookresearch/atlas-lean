# Root-to-leaf query and quotient-recovering deletion

In the multi-level dictionary tree, a query for key $u$ follows the routing permutations from the root to a single leaf, compressing $u$'s identifier at each level, and returns the payload stored in that leaf's minimap (or reports absence); the answer agrees with the represented dictionary. A deletion follows the same path, removes the key from its leaf and recovers, from the compressed identifier and the routing permutations, the quotient bits needed to maintain the parent's information-conserving encoding; insertion of a fresh key on the normal path places it in the leaf selected by routing, and in-place overwrite changes only the payload.

## Proof sketch

Each routing step is a permutation, so the path and compressed identifier of a key are uniquely determined, and storing a key below a child records exactly the bits the routing removed. Correctness of each operation is checked against the abstract map node by node.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Proof depends on

- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
