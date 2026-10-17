---
article_id: af_9319f9cb5f798efa1577f860
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.OpenAddressing.occupied_of_insert_eq_none
---

# Occupied of insert eq none

When `insert` fails, every one of the first `m` probed slots is occupied by a key
different from the inserted one. For probe sequences that are permutations of the
slots, this says exactly that the table is full with other keys.

## Depends on

- [Open Addressing](../part-01/open-addressing.md)
- [Insert](../part-01/insert.md)

## Proof depends on

- [Insert Aux](../part-01/insert-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing](../../../../../../../../sources/v2/CSLibExt.md)
