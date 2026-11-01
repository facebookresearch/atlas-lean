---
article_id: af_f449da197edb1512a146475f
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Trie.delete
---

# Delete

Delete the value at a list key. The terminal node is unmarked, and on the
way back up any child that became a childless non-terminal node is pruned
from its parent. Deleting an absent key leaves every lookup unchanged.

## Depends on

- [Trie](../../../part-03/trie/trie.md)

## Proof depends on

- [Set Child](set-child.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.Trie.Delete](../../../../../../../../sources/v2/CSLibExt.md)
