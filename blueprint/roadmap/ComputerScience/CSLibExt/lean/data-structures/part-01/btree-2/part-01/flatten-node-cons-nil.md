---
article_id: af_e976189bcaea80e15135ab55
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BTree.flatten_node_cons_nil
---

# Flatten node cons nil

Flattening a node with no children returns its separator keys in
order. This covers nodes with more keys than a well-formed node would
have.

## Depends on

- [BTree](btree.md)
- [Flatten](flatten.md)

## Proof depends on

- [Flatten Aux](flatten-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree](../../../../../../../../sources/v2/CSLibExt.md)
