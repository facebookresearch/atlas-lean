---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.free_of_free_flip
---

# Free of free flip

A left vertex unmatched after a phase was unmatched before it: the first pair of each path
starts at an unmatched right vertex, and every other right vertex of a path had the previous left
vertex as partner, which the phase rematches.

## Depends on

- [Free](../part-01/free.md)
- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Flip](../part-01/flip.md)
- [Phase](../part-03/phase.md)

## Proof depends on

- [Alt Path](../part-01/alt-path.md)
- [Is Augmenting Path](../part-01/is-augmenting-path.md)
- [Layers](../part-01/layers.md)
- [Phase Aux](../part-03/phase-aux.md)
- [Phase Aux spec](../part-03/phase-aux-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
