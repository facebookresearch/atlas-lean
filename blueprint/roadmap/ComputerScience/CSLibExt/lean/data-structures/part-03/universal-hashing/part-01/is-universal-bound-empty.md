---
article_id: af_35870e8d17020dbaa59739f0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.UniversalHashing.isUniversal_bound_empty
---

# Is Universal bound empty

The collision bound part of universality, without nonemptiness. The empty
family satisfies this bound vacuously; `IsUniversal` is this bound together with
`H.Nonempty` and a positive range size `0 < m`.

## Depends on

- [Collision Count](collision-count.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing](../../../../../../../../sources/v2/CSLibExt.md)
