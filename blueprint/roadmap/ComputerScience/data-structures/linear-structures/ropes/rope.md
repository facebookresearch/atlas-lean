# Rope

A *rope* with chunk bound $B \ge 1$ is a binary tree representing a sequence: each leaf holds a nonempty chunk of at most $B$ consecutive elements, and each internal node has two nonempty children and caches the total length of its subtree and its height. The represented sequence is the concatenation of the leaf chunks from left to right. A rope is *well formed* if its caches are correct, its leaves satisfy the chunk bound, and sibling heights differ by at most one (balance). Concatenation of two ropes creates one node, independently of their lengths.

## Depends on

- [AVL balance invariant](../../search-trees/avl-tree/balanced.md)

## Sources

- H.-J. Boehm, R. Atkinson and M. Plass, "Ropes: an Alternative to Strings", Software: Practice and Experience 25(12), 1995.
