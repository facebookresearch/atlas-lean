---
article_id: af_986886bf14660792c497e860
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SplayTree.insert
---

# Insert

Insert a key by splaying and then splitting: splay `x`, split the result
at `x`, and attach the two parts below a fresh root holding `x`. An
already-present key is splayed to the root and split off, so no duplicate
is created.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Splay](splay.md)
- [Split](split.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SplayTree](../../../../../../../../sources/v2/CSLibExt.md)
