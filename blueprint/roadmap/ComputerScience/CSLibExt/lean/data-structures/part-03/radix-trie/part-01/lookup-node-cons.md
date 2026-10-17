---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RadixTrie.lookup_node_cons
---

# Lookup node cons

Lookup of a nonempty key follows the first edge whose label starts with the key's
head, and continues below it only when the whole label prefixes the key.

## Depends on

- [Radix Trie](radix-trie.md)
- [Common Prefix](common-prefix.md)
- [Find Edge](find-edge.md)
- [Lookup](lookup.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RadixTrie](../../../../../../../../sources/v2/CSLibExt.md)
