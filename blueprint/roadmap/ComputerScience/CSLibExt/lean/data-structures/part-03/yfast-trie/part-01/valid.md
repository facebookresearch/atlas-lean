---
article_id: af_75813a1b7abf456369108ee5
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.GroupedYFastTrie.Valid
---

# Valid

The group invariant: the representative trie is a valid x-fast trie whose keys are
exactly the group maxima; every group is nonempty, has at most `B` keys, and is
strictly sorted; and the groups are ordered.

## Depends on

- [Grouped YFast Trie](grouped-yfast-trie.md)

## Proof depends on

- [Group Ordered](group-ordered.md)
- [XFast Trie](../../xfast-trie/part-01/xfast-trie.md)
- [Valid](../../xfast-trie/part-01/valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.YFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
