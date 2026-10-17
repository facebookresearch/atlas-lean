---
declaration: inductive
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RadixTrie.Valid
---

# Valid

The radix-trie invariant: at every node, edge labels are nonempty, their first symbols
are distinct, every subtree is valid, and every subtree is path-compressed at its root
(`RootCompact`): a value-free non-root node has at least two children, so no unary
value-free node remains to be merged into its parent edge.

## Depends on

- [Radix Trie](radix-trie.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RadixTrie](../../../../../../../../sources/v2/CSLibExt.md)
