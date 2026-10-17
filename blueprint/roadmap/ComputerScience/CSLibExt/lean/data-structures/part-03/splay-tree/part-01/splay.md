---
article_id: af_cb09134b6668749c0f5ce837
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SplayTree.splay
---

# Splay

Splay `x` to the root. The search descends as in a binary search tree;
the restructuring pattern-matches the child on the search path, so each
recursive step performs a zig (single rotation), a zig-zig (both
rotations in the same direction, grandparent edge first), or a zig-zag
(rotations in opposite directions, parent edge first). When `x` is
absent, the node where the search stops is what the rotations carry
upward; branches where the splayed grandchild is empty fall back to a
single zig that carries that last visited node one level up.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SplayTree](../../../../../../../../sources/v2/CSLibExt.md)
