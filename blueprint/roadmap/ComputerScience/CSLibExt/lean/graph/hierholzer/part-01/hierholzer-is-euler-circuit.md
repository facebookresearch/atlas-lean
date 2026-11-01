---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.hierholzer_isEulerCircuit
---

# Hierholzer is Euler Circuit

CLRS Problem 22-3, sufficiency with the algorithm: on a balanced graph whose edges all start
at vertices reachable from `s`, `hierholzer graph s` is an Euler circuit from `s`.

## Depends on

- [Directed Adjacency](../../directed-adjacency-2/part-01/directed-adjacency.md)
- [Edge](../../directed-adjacency-2/part-01/edge.md)
- [Reachable](../../directed-adjacency-2/part-01/reachable.md)
- [Is Balanced](is-balanced.md)
- [Is Euler Circuit](is-euler-circuit.md)
- [Hierholzer](hierholzer.md)

## Proof depends on

- [Is Semi Balanced](is-semi-balanced.md)
- [Edge List](edge-list.md)
- [Hierholzer is Euler Path](hierholzer-is-euler-path.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Hierholzer](../../../../../../../sources/v2/CSLibExt.md)
