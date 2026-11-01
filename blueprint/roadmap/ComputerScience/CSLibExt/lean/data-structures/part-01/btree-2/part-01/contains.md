---
article_id: af_f5a93e07d242c16e4d37b286
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.contains
---

# Contains

Search a tree by comparing the query key against the separators from the root down:
at each internal node descend into the first child whose following separator exceeds the
query, report success on equality with a separator, and at a leaf report membership in
the key list.

## Depends on

- [BTree](btree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
