# Root-to-leaf query and quotient-recovering deletion

In the multi-level dictionary tree (Li, Liang, Yu and Zhou, Section 5.3), every operation on a key $u$ first follows the routing permutations from $u$'s root to its leaf, recording $u$'s identifier and quotient at each level of the path. A *query* looks up $u$'s identifier in the storage table (inner nodes) or minimap (leaf) of every node on the path, since $u$ may be stored at any of them, and reports $u$ present, with its value, iff some node stores that identifier with $u$'s quotient; a stored identifier with a different quotient means $u$ is absent, because identifiers are unique within a node. An *insertion* of a fresh key puts it into its root's storage table and adds its (level-$\ell$, level-$(\ell - 1)$) identifier pair to the waiting list of every non-root node on the path. A *deletion* (Algorithm 3) starts at $u$'s leaf and walks up the path: at a node that does not store $u$, it removes $u$ from the node's waiting list, recurses to the parent, and recovers $u$'s quotient at this level from its identifier and quotient one level up; at the node $w$ storing $u$, it removes $u$ and, if $w$ is not a root, refills $w$ with an arbitrary key $y$ from $w$'s waiting list, which it first deletes recursively from $w$'s parent to learn $y$'s quotient. Each operation answers according to the represented dictionary, visits every node of the path $O(1)$ times, and takes $O(\log^* n + \log r)$ expected time; queries take $O(\log^* n)$ time.

## Proof sketch

Each routing step is a permutation, so a key's path, identifiers and quotients are uniquely determined, and the level-$(\ell - 1)$ identifier and quotient determine the level-$\ell$ ones. A key is stored at exactly one node of its path, so the query is correct; the refill keeps every non-root storage table and minimap full, and the waiting list of a node lists exactly the keys routed to it that are stored above it. Storage tables and waiting lists take $O(1)$ expected time per access and the leaf minimap $O(\log r)$ per update, over $O(\log^* n)$ levels.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)
- [Waiting list of a dictionary-tree node](waiting-list-of-a-node.md)

## Proof depends on

- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
