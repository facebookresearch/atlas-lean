---
article_id: af_232f7cb615b4c6cea1496073
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.OpenAddressing.insert
---

# Insert

Inserts a new binding or replaces the existing binding for the key, at the first
probed slot that is empty or already holds the key. Returns `none` when the first
`m` probed slots are all occupied by other keys.

## Depends on

- [Open Addressing](open-addressing.md)

## Proof depends on

- [Insert Aux](insert-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing](../../../../../../../../sources/v2/CSLibExt.md)
