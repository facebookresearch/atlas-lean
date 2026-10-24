---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.uvisit_spec
---

# Uvisit spec

The contract of `uvisit`: given more fuel than remaining edges and a remainder whose
odd-degree vertices are exactly `v` and `t` (none when `v = t`), the call emits a walk `W` from
`v` to `t` in front of `acc`, removes exactly its steps (as unordered pairs), leaves a remainder of
even degrees, a sublist of `R`, in which `W`'s vertices have no edges, and costs one unit per
removed edge.

## Depends on

- [Even Except](even-except.md)
- [Udeg](udeg.md)
- [Usym](usym.md)
- [Uvisit](uvisit.md)
- [Walk Edges](../hierholzer/part-01/walk-edges.md)

## Proof depends on

- [Other End](other-end.md)
- [Perm splice](../hierholzer/part-01/perm-splice.md)
- [Udeg erase](udeg-erase.md)
- [Usym eq other End](usym-eq-other-end.md)
- [Walk Edges append](../hierholzer/part-01/walk-edges-append.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected](../../../../../../sources/v2/CSLibExt.md)
