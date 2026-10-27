---
article_id: af_05a97287077f3906b639e96d
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.OpenAddressing.lookup
---

# Lookup

Looks up a key along its probe sequence, using at most `m` probes. Returns the value
at the first probed slot holding the key, and `none` if an empty slot or the probe
budget is reached first.

## Depends on

- [Open Addressing](open-addressing.md)

## Proof depends on

- [Lookup Aux](lookup-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OpenAddressing](../../../../../../../../sources/v2/CSLibExt.md)
