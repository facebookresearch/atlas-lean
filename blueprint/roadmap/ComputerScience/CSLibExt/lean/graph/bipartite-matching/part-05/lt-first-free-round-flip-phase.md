---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.lt_firstFreeRound_flip_phase
---

# The next phase's paths are strictly longer

**The next phase's paths are strictly longer** (Hopcroft and Karp): if `firstFreeRound` is `d`
before a phase and `d'` after it, then `d < d'`. A shortest augmenting path after the phase of the
same length would be a shortest augmenting chain before it, disjoint from the phase's paths,
contradicting `phase_maximal`'s invariant.

## Depends on

- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Flip](../part-01/flip.md)
- [Phase](../part-03/phase.md)

## Proof depends on

- [Alt Path](../part-01/alt-path.md)
- [Exact Level](../part-04/exact-level.md)
- [Free](../part-01/free.md)
- [Is Augmenting Path](../part-01/is-augmenting-path.md)
- [Is Chain From](../part-04/is-chain-from.md)
- [No Escape](../part-04/no-escape.md)
- [Chain of chain flip phase](chain-of-chain-flip-phase.md)
- [First Free Round eq some](../part-03/first-free-round-eq-some.md)
- [Layers](../part-01/layers.md)
- [Distances do not decrease across a phase](../part-04/layers-flip-phase-subset.md)
- [Le first Free Round flip phase](le-first-free-round-flip-phase.md)
- [No augmenting path is shorter than a phase's](../part-03/le-length-of-is-augmenting-path.md)
- [Phase Aux](../part-03/phase-aux.md)
- [Phase Aux maximal](../part-04/phase-aux-maximal.md)
- [Phase spec](phase-spec.md)
- [Search Path](../part-02/search-path.md)
- [Search Path is Some](../part-02/search-path-is-some.md)
- [Search Path length le](../part-04/search-path-length-le.md)
- [Search Path spec](../part-02/search-path-spec.md)
- [Valid flip flatten](../part-03/valid-flip-flatten.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
