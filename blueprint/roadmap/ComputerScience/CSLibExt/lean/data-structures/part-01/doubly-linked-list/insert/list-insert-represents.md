---
article_id: af_53300cf7eb6e16d43baeb1c0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DoublyLinkedList.listInsert_represents
---

# List Insert represents

Inserting an allocated fresh node after index `k` preserves the exact source-list
representation, with no head write. Freshness is a proof premise, not an execution guard.

## Depends on

- [Node](../basic/node.md)
- [Represents](../basic/represents.md)
- [List Insert](list-insert.md)

## Proof depends on

- [List Insert get](list-insert-get.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Insert](../../../../../../../../sources/v2/CSLibExt.md)
