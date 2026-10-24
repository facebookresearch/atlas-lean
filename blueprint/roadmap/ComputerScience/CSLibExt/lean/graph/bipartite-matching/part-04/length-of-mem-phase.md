---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.length_of_mem_phase
---

# Phases use shortest augmenting paths

**Phases use shortest augmenting paths.** If `firstFreeRound` is `d`, every path of the phase
has exactly `d + 1` pairs, the least length of any augmenting path
(`le_length_of_isAugmentingPath`).

## Depends on

- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Phase](../part-03/phase.md)

## Proof depends on

- [Is Augmenting Path](../part-01/is-augmenting-path.md)
- [Layers](../part-01/layers.md)
- [No augmenting path is shorter than a phase's](../part-03/le-length-of-is-augmenting-path.md)
- [Phase Aux](../part-03/phase-aux.md)
- [Phase Aux length le](phase-aux-length-le.md)
- [Phase Aux spec](../part-03/phase-aux-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
