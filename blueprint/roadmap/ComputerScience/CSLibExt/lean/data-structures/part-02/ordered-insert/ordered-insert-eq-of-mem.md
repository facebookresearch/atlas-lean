---
article_id: af_c70bf8afdca25f70f4bc679f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.orderedInsert_eq_of_mem
---

# Ordered Insert eq of mem

On a strictly sorted list, inserting an already-present key is a no-op.
This is the duplicate-elision contract the tree implementations rely on;
without strict sortedness it fails, e.g. `orderedInsert 2 [3, 2] = [2, 3, 2]`.

## Depends on

- [Ordered Insert](ordered-insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OrderedInsert](../../../../../../../sources/v2/CSLibExt.md)
