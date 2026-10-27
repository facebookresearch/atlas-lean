---
article_id: af_84cac60a5f72e4a4ab51da04
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.OpenAddressing.lookup_isSome_iff
---

# Lookup is Some iff

Under `Valid`, a lookup succeeds if and only if the key is stored in some slot.
This is the membership characterization used in place of a `Finmap` abstraction;
the value found is pinned down by `stored_of_lookup_eq_some` and, after an
insert, by `lookup_insert`.

## Depends on

- [Open Addressing](open-addressing.md)
- [Stored](stored.md)
- [Valid](valid.md)
- [Lookup](lookup.md)

## Proof depends on

- [Lookup is Some of stored](lookup-is-some-of-stored.md)
- [Stored of lookup eq some](stored-of-lookup-eq-some.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing](../../../../../../../../sources/v2/CSLibExt.md)
