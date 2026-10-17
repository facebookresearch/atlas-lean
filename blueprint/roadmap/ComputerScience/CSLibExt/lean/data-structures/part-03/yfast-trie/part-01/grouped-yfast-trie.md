---
article_id: af_526d8480c80e329d2081277e
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.GroupedYFastTrie
---

# Grouped YFast Trie

A grouped y-fast trie over `w`-bit keys: an x-fast trie of representatives plus the
list of groups in increasing order, with group size bounded by `B`. Each group is a
sorted list standing in for a balanced search tree; no complexity bound is claimed.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.YFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
