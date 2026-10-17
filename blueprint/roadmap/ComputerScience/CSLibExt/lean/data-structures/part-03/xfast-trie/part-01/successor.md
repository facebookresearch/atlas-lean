---
article_id: af_5340a2ada18d12638de840e7
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.XFastTrie.successor
---

# Successor

The successor of `x`: the least stored key greater than `x`, if one exists. Defined from
`contents`; the classical binary search over levels is not formalized, so no O(log w)
bound is claimed.

## Depends on

- [XFast Trie](xfast-trie.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.XFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
