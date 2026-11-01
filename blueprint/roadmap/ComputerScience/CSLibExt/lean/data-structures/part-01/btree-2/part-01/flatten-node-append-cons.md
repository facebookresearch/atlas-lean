---
article_id: af_6bbfe86616af8697e8f92c94
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_node_append_cons
---

# Flatten node append cons

Splitting a node's key and child lists at a separator splits its
flattening at that separator, provided the left lists are in the
well-formed ratio of one more child than keys.

## Depends on

- [BTree](btree.md)
- [Flatten](flatten.md)

## Proof depends on

- [Flatten Aux](flatten-aux.md)
- [Flatten Aux eq](flatten-aux-eq.md)
- [Flatten node nil cons](flatten-node-nil-cons.md)
- [Flatten node nil nil](flatten-node-nil-nil.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
