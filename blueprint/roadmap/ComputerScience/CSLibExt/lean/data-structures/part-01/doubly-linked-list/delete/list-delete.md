---
article_id: af_f18e8c69a26006e590f464c3
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DoublyLinkedList.listDelete
---

# List Delete

Delete an allocated node by identity, preserving its record and all allocations.
The two NIL tests and executed pointer assignments cost three or four events.
Only allocation access is required; list consistency is a correctness premise.

## Depends on

- [Node](../basic/node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Delete](../../../../../../../../sources/v2/CSLibExt.md)
