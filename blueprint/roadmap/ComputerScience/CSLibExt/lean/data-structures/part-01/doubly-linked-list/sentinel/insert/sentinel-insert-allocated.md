---
article_id: af_f44dae3dc4b9ab387690acca
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DoublyLinkedList.sentinelInsert_allocated
---

# Sentinel Insert allocated

Insertion neither allocates nor deallocates a cell, even with aliased targets.

## Depends on

- [Node](../../basic/node.md)
- [Sentinel Insert](sentinel-insert.md)

## Proof depends on

- [List Insert](../../insert/list-insert.md)
- [List Insert allocated](../../insert/list-insert-allocated.md)
- [List Insert ret](../../insert/list-insert-ret.md)
- [Sentinel Insert ret](sentinel-insert-ret.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Insert](../../../../../../../../../sources/v2/CSLibExt.md)
