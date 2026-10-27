---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RadixTrie.lookup_eq_some_iff_mem_entries
---

# Lookup eq some iff mem entries

Lookup succeeds exactly when the pair occurs in `entries`, for valid tries.

## Depends on

- [Radix Trie](../part-01/radix-trie.md)
- [Valid](../part-01/valid.md)
- [Entries](entries.md)
- [Lookup](../part-01/lookup.md)

## Proof depends on

- [Root Compact](../part-01/root-compact.md)
- [Append of common Prefix eq](../part-01/append-of-common-prefix-eq.md)
- [Common Prefix](../part-01/common-prefix.md)
- [Common Prefix eq of append](../part-01/common-prefix-eq-of-append.md)
- [Find Edge](../part-01/find-edge.md)
- [Lookup node cons](../part-01/lookup-node-cons.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RadixTrie](../../../../../../../../sources/v2/CSLibExt.md)
