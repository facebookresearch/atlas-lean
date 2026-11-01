---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.pair_levels_of_mem_phase
---

# Pair levels of mem phase

Every pair of a phase has its right vertex first reached in some round `m + 1` and its left
vertex reached by round `m`.

## Depends on

- [Exact Level](exact-level.md)
- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Layers](../part-01/layers.md)
- [Phase](../part-03/phase.md)

## Proof depends on

- [Alt Path](../part-01/alt-path.md)
- [Free](../part-01/free.md)
- [Is Augmenting Path](../part-01/is-augmenting-path.md)
- [First Free Round eq some](../part-03/first-free-round-eq-some.md)
- [Phases use shortest augmenting paths](length-of-mem-phase.md)
- [Mem layers length](../part-03/mem-layers-length.md)
- [Pair levels of chain](pair-levels-of-chain.md)
- [Phase Aux](../part-03/phase-aux.md)
- [Phase Aux spec](../part-03/phase-aux-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
