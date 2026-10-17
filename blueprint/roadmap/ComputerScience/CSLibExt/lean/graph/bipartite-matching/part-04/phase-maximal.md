---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.phase_maximal
---

# Phases are maximal

**Phases are maximal.** If `firstFreeRound` is `d`, every shortest augmenting path (`d + 1`
pairs, the least length by `le_length_of_isAugmentingPath`) shares a vertex with a path of the
phase: the phase's vertex-disjoint shortest augmenting paths form a maximal set, as Hopcroft and
Karp require.

## Depends on

- [Is Augmenting Path](../part-01/is-augmenting-path.md)
- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Phase](../part-03/phase.md)

## Proof depends on

- [Alt Path](../part-01/alt-path.md)
- [Exact Level](exact-level.md)
- [Free](../part-01/free.md)
- [Is Chain From](is-chain-from.md)
- [No Escape](no-escape.md)
- [First Free Round eq some](../part-03/first-free-round-eq-some.md)
- [Layers](../part-01/layers.md)
- [Mem layers length](../part-03/mem-layers-length.md)
- [Phase Aux](../part-03/phase-aux.md)
- [Phase Aux maximal](phase-aux-maximal.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
