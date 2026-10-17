---
article_id: af_ad6c4adfe2a5fc9cf08cd1de
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_node_nil_cons
---

# Flatten node nil cons

Flattening a node with no separator keys concatenates the flattenings
of its children in order. This covers nodes with more children than a
well-formed node would have.

## Depends on

- [BTree](btree.md)
- [Flatten](flatten.md)

## Proof depends on

- [Flatten Aux](flatten-aux.md)
- [Flatten Aux eq](flatten-aux-eq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
