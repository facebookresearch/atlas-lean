---
article_id: af_2c8de5d251ad6527cddf00cc
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.cloitreMirror
---

# Cloitre Mirror

Mirror image with first-letter complementation: `A^r`.

Reverses `A` and flips its first run-letter (`[1, 1] ↔ [2]`). For example
`[1, 1, 2]^r = [1, 1, 1, 1]` and `[1, 1, 2, 1, 1, 1, 1]^r = [2, 1, 1, 2, 1, 1]`.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cloitre Complement First](cloitre-complement-first.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.InfiniteWord.CloitreSequence](../../../../../../sources/v2/MathlibExt.md)
