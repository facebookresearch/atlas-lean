---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.RadixTrie.hasPrefix_eq_true_iff
---

# Has Prefix eq true iff

Prefix search succeeds exactly when some stored key extends the pattern.

## Depends on

- [Radix Trie](../part-01/radix-trie.md)
- [Valid](../part-01/valid.md)
- [Has Prefix](has-prefix.md)
- [Keys](keys.md)

## Proof depends on

- [Root Compact](../part-01/root-compact.md)
- [Append drop common Prefix left](../part-01/append-drop-common-prefix-left.md)
- [Common Prefix](../part-01/common-prefix.md)
- [Common Prefix eq of append](../part-01/common-prefix-eq-of-append.md)
- [Common Prefix spec](../part-01/common-prefix-spec.md)
- [Entries](entries.md)
- [Find Edge](../part-01/find-edge.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RadixTrie](../../../../../../../../sources/v2/CSLibExt.md)
