---
article_id: af_158138e210edb4d1b9f1a862
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SinglyLinkedList.deleteAfter
---

# Delete After

Delete the successor of the allocated node `y` by splicing `y` past it.
The removed node stays allocated; at the tail this is a no-op on links.

## Depends on

- [Node](../part-01/node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SinglyLinkedList](../../../../../../../../sources/v2/CSLibExt.md)
