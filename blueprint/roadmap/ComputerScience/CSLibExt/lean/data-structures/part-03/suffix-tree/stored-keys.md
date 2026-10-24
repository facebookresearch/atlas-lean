---
article_id: af_cf70e6b5736dab2dcc471fbd
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SuffixTree.storedKeys
---

# Stored Keys

The stored keys of the suffix tree: exactly the terminated suffixes.
This is a statement about stored keys, not about structural trie leaves;
`RadixTrie.Valid` permits values at internal nodes in general, and no
leaf characterization is claimed.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Keys](../radix-trie/part-02/keys.md)
- [Suffix Tree](suffix-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SuffixTree](../../../../../../../sources/v2/CSLibExt.md)
