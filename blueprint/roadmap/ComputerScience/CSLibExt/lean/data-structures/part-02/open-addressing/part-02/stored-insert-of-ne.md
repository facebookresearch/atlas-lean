---
article_id: af_3392c05122ed42c780c5d108
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.OpenAddressing.stored_insert_of_ne
---

# Stored insert of ne

A successful insert changes no other key's stored binding: for `other ≠ key`,
`other ↦ otherValue` is stored after the insert exactly when it was stored
before. No validity assumption is needed; the insert writes a single slot,
previously empty or previously holding `key`, and leaves every other slot
unchanged.

## Depends on

- [Open Addressing](../part-01/open-addressing.md)
- [Stored](../part-01/stored.md)
- [Insert](../part-01/insert.md)

## Proof depends on

- [Insert Aux](../part-01/insert-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing](../../../../../../../../sources/v2/CSLibExt.md)
