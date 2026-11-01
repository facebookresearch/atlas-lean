---
article_id: af_de1542df12568e566632d9a7
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.DynamicTable.tableDelete
---

# Table Delete

TABLE-DELETE for the last item. After decrementing `num`, contract to half
capacity when `4 * num < size`, that is, when the new load factor is
strictly below `1/4`; otherwise clear the vacated slot in place.

## Depends on

- [Table](../basic/part-01/table.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.DynamicTable.Delete](../../../../../../../../sources/v2/CSLibExt.md)
