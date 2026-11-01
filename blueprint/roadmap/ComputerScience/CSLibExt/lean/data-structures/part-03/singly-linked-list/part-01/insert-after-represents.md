---
article_id: af_3baabfa7f43984fe2ba83555
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SinglyLinkedList.insertAfter_represents
---

# Insert After represents

Inserting a fresh allocated node after position `k` inserts its identity at
position `k + 1` of the represented list; the header is unchanged.

## Depends on

- [Node](node.md)
- [Represents](represents.md)
- [Insert After](insert-after.md)

## Proof depends on

- [Insert After get](insert-after-get.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SinglyLinkedList](../../../../../../../../sources/v2/CSLibExt.md)
