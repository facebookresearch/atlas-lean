---
article_id: af_83e7b0dc01331aedad3246a7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SinglyLinkedList.deleteAfter_represents
---

# Delete After represents

Deleting the successor of position `k` erases position `k + 1` of the
represented list (a no-op at the tail); the header is unchanged.

## Depends on

- [Node](../part-01/node.md)
- [Represents](../part-01/represents.md)
- [Delete After](delete-after.md)

## Proof depends on

- [Delete After frame](delete-after-frame.md)
- [Delete After get](delete-after-get.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SinglyLinkedList](../../../../../../../../sources/v2/CSLibExt.md)
