---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.le_firstFreeRound_flip_phase
---

# Le first Free Round flip phase

The next phase's paths are at least as long: if `firstFreeRound` is `d` before a phase and
`d'` after it, then `d ≤ d'`.

## Depends on

- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Flip](../part-01/flip.md)
- [Phase](../part-03/phase.md)

## Proof depends on

- [First Free Round eq some](../part-03/first-free-round-eq-some.md)
- [Layers](../part-01/layers.md)
- [Distances do not decrease across a phase](../part-04/layers-flip-phase-subset.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
