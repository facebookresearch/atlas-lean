---
article_id: af_b989c8b145b1341cd33663b5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.SuffixTree.storedKeys_length
---

# Stored Keys length

The suffix tree stores exactly `s.length + 1` keys, one per terminated
suffix.

## Depends on

- [Stored Keys](stored-keys.md)

## Proof depends on

- [Valid](../radix-trie/part-01/valid.md)
- [Empty](../radix-trie/part-02/empty.md)
- [Insert](../radix-trie/part-02/insert.md)
- [Keys nodup](../radix-trie/part-02/keys-nodup.md)
- [Build From](../radix-trie/part-02/build-from.md)
- [Mem suffix Tree keys](mem-suffix-tree-keys.md)
- [Nodup terminated drops](nodup-terminated-drops.md)
- [Suffix Entries](suffix-entries.md)
- [Suffix Tree](suffix-tree.md)
- [Terminated](terminated.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SuffixTree](../../../../../../../sources/v2/CSLibExt.md)
