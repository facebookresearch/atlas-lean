---
article_id: af_f12ce957acaad3f08a54e880
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.rerootAt
---

# Reroot At

Reroot a tree at `x`, reversing the edges on the path from the old root
to `x` and keeping every other edge: the undirected tree is unchanged, only
the choice of root changes. Returns `none` when `x` does not occur. This is
the tree surgery behind `State.makeRoot`.

The recursion reroots the child subtree `c` on the root-to-`x` path first,
then grafts the remainder of the current node (the old root `r` together
with the sibling subtrees off the path) back under the root of `c`, which
is the next vertex on the reversed path. Attaching the remainder under
that path vertex, rather than directly under `x`, is what keeps every
path edge intact at depth greater than one.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)

## Proof depends on

- [Root](../../euler-tour-tree/part-01/root.md)
- [Graft At](graft-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
