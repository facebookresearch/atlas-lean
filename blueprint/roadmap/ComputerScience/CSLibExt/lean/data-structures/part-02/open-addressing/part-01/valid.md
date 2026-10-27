---
article_id: af_e1997bfab3c0fb99ab914a56
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.OpenAddressing.Valid
---

# Valid

The validity invariant, in two parts. Probe-closedness: every stored binding is
reached by its key's probe sequence within `m` probes, and every earlier probed
slot is occupied; this is the property that lets `lookup` stop at the first empty
slot. Key uniqueness: no key is stored in two different slots, so each key has at
most one binding and `insert` genuinely replaces it (see `stored_unique` and
`lookup_eq_some_iff`).

## Depends on

- [Open Addressing](open-addressing.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing](../../../../../../../../sources/v2/CSLibExt.md)
