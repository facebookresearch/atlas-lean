---
article_id: af_d1f54914746cc42739001960
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.CallanSequence
---

# Callan Sequence

Unbarred `Callan sequence` of size `k × n` (concept
`jis_term_ce5e63b2f9fff90839347b2c`, statement `jis_9bd5ee64b3776e07257d0f5f`,
source `jis_source_076226dadb590961d2a14ace`, lines 159-190).

The blue base set `{1, …, k} ∪ {*}` is represented as `Option (Fin k)` with
`none` the distinguished blue star, and likewise the red base set is
`Option (Fin n)` with `none` the red star. The `m + 1` ordered Callan pairs
are indexed by `Fin (m + 1)`, with `Fin.last m` indexing the extra pair
`(B⋆, R⋆)` that contains both stars. Each colour's blocks are nonempty and
every base-set element belongs to exactly one block.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CallanSequence](../../../../../../sources/v2/MathlibExt.md)
