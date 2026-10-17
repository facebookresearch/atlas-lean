---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.hierholzer_trail
---

# Hierholzer trail

On a semi-balanced graph the result is a walk from `s` to `t` that uses each edge occurrence
at most once (closed when `s = t`).

## Depends on

- [Directed Adjacency](../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Is Semi Balanced](is-semi-balanced.md)
- [Edge List](edge-list.md)
- [Hierholzer](hierholzer.md)
- [Walk Edges](walk-edges.md)

## Proof depends on

- [Balanced Edges](balanced-edges.md)
- [Edge List Of](edge-list-of.md)
- [Visit](visit.md)
- [Visit spec](visit-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Hierholzer](../../../../../../../sources/v2/CSLibExt.md)
