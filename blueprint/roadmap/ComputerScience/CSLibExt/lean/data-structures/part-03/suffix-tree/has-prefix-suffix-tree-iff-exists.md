---
article_id: af_ef61b98d7345643175917686
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SuffixTree.hasPrefix_suffixTree_iff_exists
---

# Has Prefix suffix Tree iff exists

Prefix lookup in the suffix tree succeeds exactly when the pattern prefixes some
suffix of `s`.

## Depends on

- [Has Prefix](../radix-trie/part-02/has-prefix.md)
- [Suffix Tree](suffix-tree.md)

## Proof depends on

- [Valid](../radix-trie/part-01/valid.md)
- [Empty](../radix-trie/part-02/empty.md)
- [Insert](../radix-trie/part-02/insert.md)
- [Build From](../radix-trie/part-02/build-from.md)
- [Has Prefix eq true iff](../radix-trie/part-02/has-prefix-eq-true-iff.md)
- [Keys](../radix-trie/part-02/keys.md)
- [Is Prefix of map some prefix append none](is-prefix-of-map-some-prefix-append-none.md)
- [Mem suffix Tree keys](mem-suffix-tree-keys.md)
- [Suffix Entries](suffix-entries.md)
- [Terminated](terminated.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SuffixTree](../../../../../../../sources/v2/CSLibExt.md)
