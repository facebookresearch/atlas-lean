---
article_id: af_46f0ecdfbd03cfd005729bba
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.orderedInsert
---

# Ordered Insert

Insert a key into a list at its sorted position: the scan stops at the
first element that is not smaller than the key and stops there, so a key
already present is ignored only when the list is strictly sorted (see
`orderedInsert_eq_of_mem`); on an unsorted list a later duplicate is not
detected. This is the list-level specification of tree insertion.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OrderedInsert](../../../../../../../sources/v2/CSLibExt.md)
