---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.chain_of_chain_flip_phase
---

# Chain of chain flip phase

A shortest chain after a phase, from a right vertex first reached in the same round before and
after it, is a chain before the phase too, and its right vertices after the first are not on the
phase's paths: a flipped edge would step back a round, which a shortest chain cannot afford.

## Depends on

- [Exact Level](../part-04/exact-level.md)
- [Is Chain From](../part-04/is-chain-from.md)
- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Flip](../part-01/flip.md)
- [Phase](../part-03/phase.md)

## Proof depends on

- [Tail](../part-04/tail.md)
- [Free](../part-01/free.md)
- [Is Augmenting Path](../part-01/is-augmenting-path.md)
- [Free of free flip](../part-04/free-of-free-flip.md)
- [Layers](../part-01/layers.md)
- [Distances do not decrease across a phase](../part-04/layers-flip-phase-subset.md)
- [Mem layers snd of mate](../part-04/mem-layers-snd-of-mate.md)
- [Pair levels of chain](../part-04/pair-levels-of-chain.md)
- [Pair levels of mem phase](../part-04/pair-levels-of-mem-phase.md)
- [Phase spec](phase-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
