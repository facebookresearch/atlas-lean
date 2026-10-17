---
article_id: af_d2968ccd06b6a3325022aa18
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Trie.lookup_delete_of_ne
---

# Lookup delete of ne

Deleting one key does not change the lookup result for a distinct
key.

## Depends on

- [Trie](../../../part-03/trie/trie.md)
- [Delete](delete.md)
- [Lookup](../../../part-03/trie/lookup.md)

## Proof depends on

- [Is Empty Node](is-empty-node.md)
- [Is Empty Node eq true iff](is-empty-node-eq-true-iff.md)
- [Lookup empty](../../../part-03/trie/lookup-empty.md)
- [Lookup set Child of ne](lookup-set-child-of-ne.md)
- [Lookup set Child self](lookup-set-child-self.md)
- [Set Child](set-child.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.Trie.Delete](../../../../../../../../sources/v2/CSLibExt.md)
