---
article_id: af_40d6e2adfe9ab316af8c4029
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.GroupedYFastTrie.ofSortedList
---

# Of Sorted List

Build a grouped y-fast trie from a sorted list by cutting it into groups
of at most `B` keys. The bound and validity require `0 < B`
(`valid_ofSortedList`); at `B = 0` the groups degenerate to `[l]` and the
result is invalid for nonempty `l` (`not_valid_ofSortedList_zero`).

## Depends on

- [Grouped YFast Trie](../part-01/grouped-yfast-trie.md)

## Proof depends on

- [Chunk Groups](chunk-groups.md)
- [Of Groups](../part-01/of-groups.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.YFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
