---
article_id: af_db5f3fa5daefdaa15026f6fc
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.GroupedYFastTrie.chunkGroups
---

# Chunk Groups

Split a list into consecutive chunks (groups) of length at most `B`.
The length bound holds only for `0 < B` (see `chunkGroups_spec`): at
`B = 0` this degenerates to a single chunk `[l]` for nonempty `l`
(`chunkGroups_zero_of_ne`), whose length exceeds `0`. Callers needing the
bound must supply `0 < B`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Chunk Groups Aux](chunk-groups-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.YFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
