---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RadixTrie.buildFrom
---

# Build From

The trie built from a list of key-value pairs by inserting the head pair last. Later
pairs in the list are inserted first, so on duplicate keys the head-most value wins.

## Depends on

- [Radix Trie](../part-01/radix-trie.md)

## Proof depends on

- [Empty](../part-01/empty.md)
- [Insert](../part-01/insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RadixTrie](../../../../../../../../sources/v2/CSLibExt.md)
