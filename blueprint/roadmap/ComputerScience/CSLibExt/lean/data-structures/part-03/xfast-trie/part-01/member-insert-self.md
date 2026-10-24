---
article_id: af_c9f695563b5565473cf03e5c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.XFastTrie.member_insert_self
---

# Member insert self

A key is a member immediately after its own insertion, with no
validity assumption on `t`: insertion puts the full-length prefix of `x`
directly into the deepest level that `member` probes.

## Depends on

- [XFast Trie](xfast-trie.md)
- [Insert](insert.md)
- [Member](member.md)

## Proof depends on

- [Has Prefix](has-prefix.md)
- [Prefix Of](prefix-of.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.XFastTrie](../../../../../../../../sources/v2/CSLibExt.md)
