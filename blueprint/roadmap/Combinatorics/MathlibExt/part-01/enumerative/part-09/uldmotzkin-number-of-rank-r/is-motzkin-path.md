---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.ULDMotzkin.IsMotzkinPath
---

# Is Motzkin Path

A sequence of exactly `n` admissible steps is a Motzkin path when every
prefix height (computed from the actual steps by `pathHeight`) is
nonnegative and the final height is zero. Requires the source rank
hypothesis `1 ≤ r`. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`.

## Depends on

- [ULDMotzkin Step](uldmotzkin-step.md)

## Proof depends on

- [Path Height](path-height.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR](../../../../../../../sources/v2/MathlibExt.md)
