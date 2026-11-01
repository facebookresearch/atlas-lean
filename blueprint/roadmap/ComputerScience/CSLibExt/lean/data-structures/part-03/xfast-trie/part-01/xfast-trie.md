---
article_id: af_8117ab003648f6b34a8d57ca
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.XFastTrie
---

# XFast Trie

An x-fast trie over `w`-bit keys: the stored key set together with one prefix set per
level. The classical per-level hash tables are modeled as `Finset`s, so no O(log w)
successor bound (or any other running-time bound) is claimed.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.XFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
