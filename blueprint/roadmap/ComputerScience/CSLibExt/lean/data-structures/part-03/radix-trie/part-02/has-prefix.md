---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RadixTrie.hasPrefix
---

# Has Prefix

Whether some key stored in the trie extends `p`. The walk follows the edge whose label
starts with the pattern's head symbol; it succeeds when the pattern ends inside that
edge (with a stored key below) or at a node reached by consuming whole edges.

## Depends on

- [Radix Trie](../part-01/radix-trie.md)

## Proof depends on

- [Common Prefix](../part-01/common-prefix.md)
- [Find Edge](../part-01/find-edge.md)
- [Keys](keys.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RadixTrie](../../../../../../../../sources/v2/CSLibExt.md)
