---
article_id: af_fb3c0faef68713691ccd4a82
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.GroupedYFastTrie.not_valid_ofSortedList_zero
---

# Not valid of Sorted List zero

At `B = 0`, building from a nonempty list cannot be valid: the single
degenerate group `l` has positive length, violating the `≤ 0` group bound
in `Valid`. Use `0 < B` (see `valid_ofSortedList`).

## Depends on

- [Valid](../part-01/valid.md)
- [Of Sorted List](of-sorted-list.md)

## Proof depends on

- [Grouped YFast Trie](../part-01/grouped-yfast-trie.md)
- [Group Ordered](../part-01/group-ordered.md)
- [Chunk Groups zero of ne](chunk-groups-zero-of-ne.md)
- [XFast Trie](../../xfast-trie/part-01/xfast-trie.md)
- [Valid](../../xfast-trie/part-01/valid.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.YFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
