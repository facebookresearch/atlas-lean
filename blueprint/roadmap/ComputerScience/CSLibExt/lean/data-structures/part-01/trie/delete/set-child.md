---
article_id: af_3f848b399cf7a536afbba932
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Trie.setChild
---

# Set Child

Replace the child stored at `key` by `child`, dropping the entry entirely
when `child` is a childless non-terminal node. The first entry at `key` is
replaced in place (or dropped, when pruning) and any later entries at `key`
are removed, so the order of the surviving entries is preserved and at
most one entry for `key` remains even in a trie that does not satisfy
`Valid`. In `delete`, `key` is always present; for an absent key a
non-empty child is appended at the end. Its public specification is
`lookup_setChild_self`, `lookup_setChild_of_ne`, and `setChild_valid`
below.

## Depends on

- [Trie](../../../part-03/trie/trie.md)

## Proof depends on

- [Is Empty Node](is-empty-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.Trie.Delete](../../../../../../../../sources/v2/CSLibExt.md)
