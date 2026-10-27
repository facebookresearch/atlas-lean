---
article_id: af_77770eed13552a5453f5ee61
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Trie.setChild_valid
---

# Set Child valid

`setChild` preserves the child-list half of trie validity: the child
keys stay duplicate-free and every surviving child stays valid.

## Depends on

- [Trie](../../../part-03/trie/trie.md)
- [Valid](../../../part-03/trie/valid.md)
- [Set Child](set-child.md)

## Proof depends on

- [Is Empty Node](is-empty-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.Trie.Delete](../../../../../../../../sources/v2/CSLibExt.md)
