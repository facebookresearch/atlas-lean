---
article_id: af_7a8ec658e3a9ca9462489296
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DynamicTable.tableInsert
---

# Table Insert

TABLE-INSERT: allocate first, copy when full, then write the new payload.
Each actual old-item copy and the new-item write contributes one tick.

## Depends on

- [Table](table.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.DynamicTable.Basic](../../../../../../../../../sources/v2/CSLibExt.md)
